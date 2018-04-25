%% -------------------------------------------------------------------
%%
%% Copyright (c) 2014 SyncFree Consortium.  All Rights Reserved.
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
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% -------------------------------------------------------------------

%% antidote_crdt.erl : behaviour for op-based CRDTs
%% Naming pattern of antidote crdts: <type>_<semantics>
%% if there is only one kind of semantics implemented for a certain type
%% only the type is used in the name e.g. rga
%% counter_pn: PN-Counter aka Posistive Negative Counter
%% counter_b: Bounded Counter
%% counter_fat: Fat Counter
%% integer: Integer (Experimental)
%% flag_ew: Enable Wins Flag aka EW-Flag
%% flag_dw: Disable Wins Flag DW-Flag
%% set_go: Grow Only Set aka G-Set
%% set_aw: Add Wins Set aka AW-Set, previously OR-Set (Observed Remove Set)
%% set_rw: Remove Wins Set aka RW-Set
%% register_lww: Last Writer Wins Register aka LWW-Reg
%% register_mv: MultiValue Register aka MV-Reg
%% map_go: Grow Only Map aka G-Map
%% map_aw: Add Wins Map aka AW-Map (Experimental)
%% map_rr: Recursive Resets Map akak RR-Map
%% rga: Replicated Growable Array (Experimental)



-module(antidote_crdt).

-define(CRDTS, [antidote_crdt_counter_pn,
                antidote_crdt_counter_b,
                antidote_crdt_counter_fat,
                antidote_crdt_flag_ew,
                antidote_crdt_flag_dw,
                antidote_crdt_set_go,
                antidote_crdt_set_aw,
                antidote_crdt_set_rw,
                antidote_crdt_register_lww,
                antidote_crdt_register_mv,
                antidote_crdt_map_go,
                antidote_crdt_map_rr]).

-export([is_type/1,
        new/1,
        value/2,
        downstream/3,
        update/3,
        require_state_downstream/2,
        is_operation/2,
        equal/3,
        to_binary/2,
        from_binary/2
        ]).

-type internal_state() :: term().
-type internal_update() :: {atom(), term()}.
-type internal_effect() :: term().
-type internal_value() ::  term().
-type reason() :: term().

-type crdt_type() ::
      antidote_crdt_counter_pn
    | antidote_crdt_counter_b
    | antidote_crdt_counter_fat
    | antidote_crdt_flag_ew
    | antidote_crdt_flag_dw
    | antidote_crdt_set_go
    | antidote_crdt_set_aw
    | antidote_crdt_set_rw
    | antidote_crdt_register_lww
    | antidote_crdt_register_mv
    | antidote_crdt_map_go
    | antidote_crdt_map_rr.
-opaque crdt() :: 'crdt_state'. % not true, but dialyzer won't know
-type update() :: {Name::atom(), Args::any()}.
-opaque effect() :: 'crdt_effect'. % not true, but dialyzer won't know
-type value() :: any().


-export_type([ crdt_type/0,
               crdt/0,
               update/0,
               effect/0,
               value/0
             ]).



-callback new() -> internal_state().
-callback value(internal_state()) -> internal_value().
-callback downstream(internal_update(), internal_state()) -> {ok, internal_effect()} | {error, reason()}.
-callback update(internal_effect(), internal_state()) ->  {ok, internal_state()}.
-callback require_state_downstream(internal_update()) -> boolean().
-callback is_operation(internal_update()) ->  boolean(). %% Type check

-callback equal(internal_state(), internal_state()) -> boolean().
-callback to_binary(internal_state()) -> binary().
-callback from_binary(binary()) -> {ok, internal_state()} | {error, reason()}.

%% Following callbacks taken from riak_dt
%% Not sure if it is useful for antidote
%-callback stats(internal_state()) -> [{atom(), number()}].
%-callback stat(atom(), internal_state()) ->  number() | undefined.

-spec is_type(crdt_type()) -> true.
is_type(Type) ->
    is_atom(Type) andalso lists:member(Type, ?CRDTS).

-spec new(crdt_type()) -> crdt().
new(Type) -> Type:new().

-spec value(crdt_type(), crdt()) -> any().
value(Type, State) -> Type:value(State).

-spec downstream(crdt_type(), crdt(), update()) -> {ok, effect()} | {error, reason()}.
downstream(Type, State, Update) -> Type:downstream(Update, State).

-spec update(crdt_type(), crdt(), effect()) -> {ok, crdt()}.
update(Type, State, Eff) -> Type:update(Eff, State).

-spec require_state_downstream(crdt_type(), update()) -> boolean().
require_state_downstream(Type, Upd) -> Type:require_state_downstream(Upd).

-spec is_operation(crdt_type(), update()) -> boolean().
is_operation(Type, Upd) -> Type:is_operation(Upd).

-spec equal(crdt_type(), crdt(), crdt()) -> boolean().
equal(Type, State, State) -> Type:equal(State, State).

-spec to_binary(crdt_type(), crdt()) -> binary().
to_binary(Type, State) -> Type:to_binary(State).

-spec from_binary(crdt_type(), binary()) -> {ok, crdt()} | {error, reason()}.
from_binary(Type, Bin) -> Type:from_binary(Bin).

%% End of Module.
