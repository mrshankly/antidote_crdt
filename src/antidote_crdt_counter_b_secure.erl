%% -------------------------------------------------------------------
%%
%% Copyright <2013-2018> <
%%  Technische Universität Kaiserslautern, Germany
%%  Université Pierre et Marie Curie / Sorbonne-Université, France
%%  Universidade NOVA de Lisboa, Portugal
%%  Université catholique de Louvain (UCL), Belgique
%%  INESC TEC, Portugal
%% >
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either expressed or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% List of the contributors to the development of Antidote: see AUTHORS file.
%% Description and complete License: see LICENSE file.

%% -------------------------------------------------------------------
%% -*- coding: utf-8 -*-
%% --------------------------------------------------------------------------
%%
%% antidote_crdt_counter_b: A convergent, replicated, operation-based bounded counter.
%%
%% --------------------------------------------------------------------------

%% @doc
%% An operation based implementation of the bounded counter CRDT.
%% This counter is able to maintain a non-negative value by
%% explicitly exchanging permissions to execute decrement operations.
%% All operations on this CRDT are monotonic and do not keep extra tombstones.
%% @end

-module(antidote_crdt_counter_b_secure).

-behaviour(antidote_crdt).

-include("antidote_crdt.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Call backs
-export([ new/0,
          value/1,
          downstream/2,
          update/2,
          equal/2,
          to_binary/1,
          from_binary/1,
          is_operation/1,
          require_state_downstream/1
        ]).

%% API
-export([ localPermissions/2,
          permissions/1
        ]).

-export_type([ antidote_crdt_counter_b_secure/0,
               antidote_crdt_counter_b_secure_op/0,
               id/0
            ]).

-type antidote_crdt_counter_b_secure() :: {orddict:orddict(), orddict:orddict(), integer()}.

-type antidote_crdt_counter_b_secure_op() :: antidote_crdt_counter_b_secure_anon_op() | antidote_crdt_counter_b_secure_src_op().

-type antidote_crdt_counter_b_secure_anon_op() :: {transfer, {pos_integer(), id(), id()}}
                                                | {increment, {pos_integer(), pos_integer(), id()}}
                                                | {increment, {pos_integer(), id()}}
                                                | {decrement, {pos_integer(), pos_integer(), id()}}
                                                | {decrement, {pos_integer(), id()}}.

-type antidote_crdt_counter_b_secure_src_op() :: {antidote_crdt_counter_b_secure_anon_op(), id()}.

-type id() :: term(). %% A replica's identifier.

%% @doc Return a new, empty secure bound counter.
-spec new() -> antidote_crdt_counter_b_secure().
new() ->
    {orddict:new(), orddict:new(), 0}.

paillier_sum([H|T], NSquare) ->
    lists:foldl(fun(Delta, Acc) -> (Acc * Delta) rem NSquare end, H, T);
paillier_sum([], _) ->
    nil.

%% @doc Return the available permissions of replica `Id' in a `antidote_crdt_counter_b()'.
-spec localPermissions(id(), antidote_crdt_counter_b_secure()) -> non_neg_integer().
localPermissions(Id, {P, D, NSquare}) ->
    Received = lists:filtermap(
        fun
            ({{_, To}, Value}) when To == Id ->
                {true, Value};
            (_) ->
                false
        end,
        P
    ),
    Granted = lists:filtermap(
        fun
            ({{From, To}, Value}) when From == Id andalso To /= Id ->
                {true, Value};
            (_) ->
                false
        end,
        P
    ),
    case orddict:find(Id, D) of
        {ok, Decrements} ->
            {paillier_sum(Received, NSquare), paillier_sum(Granted, NSquare), Decrements};
        error ->
            {paillier_sum(Received, NSquare), paillier_sum(Granted, NSquare), nil}
    end.

%% @doc Return the total available permissions in a `antidote_crdt_counter_b()'.
-spec permissions(antidote_crdt_counter_b_secure()) -> {non_neg_integer() | nil, non_neg_integer() | nil}.
permissions({P, D, NSquare}) ->
    Increments = lists:filtermap(
        fun
            ({{K, K}, Value}) ->
                {true, Value};
            (_) ->
                false
        end,
        P
    ),
    Decrements = lists:map(fun ({_, Value}) -> Value end, D),
    {paillier_sum(Increments, NSquare), paillier_sum(Decrements, NSquare)}.

%% @doc Return the read value of a given `antidote_crdt_counter_b_secure()', itself.
value(SecureBCounter) ->
    permissions(SecureBCounter).

%% @doc Generate a downstream operation.
%% The first parameter is either `{increment, pos_integer()}' or `{decrement, pos_integer()}',
%% which specify the operation and amount, or `{transfer, pos_integer(), id()}'
%% that additionally specifies the target replica.
%% The second parameter is an `actor()' who identifies the source replica,
%% and the third parameter is a `antidote_crdt_counter_b_secure()' which holds the current snapshot.
%%
%% Return a tuple containing the operation and source replica.
%% This operation fails and returns `{error, no_permissions}'
%% if it tries to consume resources unavailable to the source replica
%% (which prevents logging of forbidden attempts).
-spec downstream(antidote_crdt_counter_b_secure_op(), antidote_crdt_counter_b_secure()) -> {ok, term()} | {error, no_permissions}.

downstream({increment, {V, NSquare, Actor}}, _Counter) when is_integer(V), V > 0 ->
    {ok, {{increment, V, NSquare}, Actor}};
downstream({increment, {V, Actor}}, _Counter) when is_integer(V), V > 0 ->
    {ok, {{increment, V}, Actor}};

downstream({decrement, {V, NSquare, Actor}}, _Counter) when is_integer(V), V > 0 ->
    {ok, {{decrement, V, NSquare}, Actor}};
downstream({decrement, {V, Actor}}, _Counter) when is_integer(V), V > 0 ->
    {ok, {{decrement, V}, Actor}};

downstream({transfer, {V, To, Actor}}, _Counter) when is_integer(V), V > 0 ->
    {ok, {transfer, V, To}, Actor}.

%% @doc Update a `antidote_crdt_counter_b()' with a downstream operation,
%% usually created with `generate_downstream'.
%%
%% Return the resulting `antidote_crdt_counter_b()' after applying the operation.
-spec update(term(), antidote_crdt_counter_b_secure()) -> {ok, antidote_crdt_counter_b_secure()}.
update({{increment, V, NSquare}, Id}, {P, D, _}) ->
    {ok, {update_permissions({Id, Id}, V, NSquare, P), D, NSquare}};
update({{increment, V}, Id}, {P, D, NSquare}) ->
    {ok, {update_permissions({Id, Id}, V, NSquare, P), D, NSquare}};
update({{decrement, V, NSquare}, Id}, {P, D, _}) ->
    {ok, {P, update_permissions(Id, V, NSquare, D), NSquare}};
update({{decrement, V}, Id}, {P, D, NSquare}) ->
    {ok, {P, update_permissions(Id, V, NSquare, D), NSquare}};
update({{transfer, _V, _To}, _From}, {_P, _D, _NSquare} = SecureBCounter) ->
    % TODO
    {ok, SecureBCounter}.

%% Add a given amount of permissions to a replica.
update_permissions(Key, Delta, NSquare, Dict) ->
    case orddict:find(Key, Dict) of
        {ok, Value} ->
            orddict:store(Key, (Value * Delta) rem NSquare, Dict);
        error ->
            orddict:store(Key, Delta, Dict)
    end.

%% doc Return the binary representation of a `antidote_crdt_counter_b_secure()'.
-spec to_binary(antidote_crdt_counter_b_secure()) -> binary().
to_binary(SecureBCounter) ->
    term_to_binary(SecureBCounter).

%% doc Return a `antidote_crdt_counter_b_secure()' from its binary representation.
-spec from_binary(binary()) -> {ok, binary()}.
from_binary(<<Bin/binary>>) ->
    {ok, binary_to_term(Bin)}.

%% @doc The following operation verifies
%%      that Operation is supported by this particular CRDT.
-spec is_operation(term()) -> boolean().
is_operation(Operation) ->
    case Operation of
        {increment, {Number, NSquare}} ->
            is_integer(Number) and is_integer(NSquare);
        {increment, Number} ->
            is_integer(Number);

        {decrement, {Number, NSquare}} ->
            is_integer(Number) and is_integer(NSquare);
        {decrement, Number} ->
            is_integer(Number);

        {transfer, {Number, _From, _To}} ->
            is_integer(Number);

        _ ->
            false
    end.

require_state_downstream(_) ->
     false.

equal(SecureBCounter1, SecureBCounter2) ->
    SecureBCounter1 == SecureBCounter2.
