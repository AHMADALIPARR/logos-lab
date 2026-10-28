% SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
% Copyright Ahmad Ali Parr
%
% Fiduciary layer of the tripartite execution lock (OWL 2 DL -> Prolog -> Boogie).
% Every agent state change passes gate/5 before the WORM SealRecursion handoff.

:- module(trust_gate,
          [ trust_deed/2,
            can_use/2,
            shrew_cut/3,
            gate/5,
            max_context_tokens/1,
            max_hash_slots/1,
            max_mem_len/1,
            demo/0
          ]).

:- use_module(library(semweb/rdf_db)).
:- use_module(library(semweb/rdfs)).

:- rdf_register_prefix(scm, 'https://snapkitty.example/scm#').

% Load the OWL anchor relative to this file.
:- prolog_load_context(directory, Dir),
   directory_file_path(Dir, 'schema.owl', File),
   rdf_load(File, [format(xml), silent(true)]).

% Spendthrift limits, mirrored as constants in state_trap.bpl.
max_context_tokens(4096).
max_hash_slots(16).
max_mem_len(65536).

% Trust deeds.
trust_deed(agent_alpha, cap_seal_recursion).
trust_deed(agent_alpha, cap_read_mesh).
trust_deed(agent_beta,  cap_read_mesh).
trust_deed(agent_ghost, cap_read_mesh).

% Expand a local name to its IRI; full IRIs pass through unchanged.
scm_iri(Name, IRI) :-
    atom(Name),
    (   sub_atom(Name, _, _, _, ':')
    ->  IRI = Name
    ;   rdf_global_id(scm:Name, IRI)
    ).

typed_in_anchor(Name, ClassLocal) :-
    scm_iri(Name, IRI),
    scm_iri(ClassLocal, Class),
    rdfs_individual_of(IRI, Class).

% An agent may use a capability only if a deed exists and both are typed in the graph.
can_use(Agent, Capability) :-
    trust_deed(Agent, Capability),
    typed_in_anchor(Agent, 'Agent'),
    typed_in_anchor(Capability, 'Capability').

% Signal filter: anything not a ProvenSignal individual in the anchor is sker_noise.
shrew_cut(Signal, _Context, Result) :-
    \+ typed_in_anchor(Signal, 'ProvenSignal'),
    !,
    Result = sker_noise.
shrew_cut(Signal, _Context, proven(Signal)).

% Deterministic hash slot derived from the gated request.
hash_slot(Agent, Capability, Signal, Hash-Slot) :-
    variant_sha1(h(Agent, Capability, Signal), Sha),
    sub_atom(Sha, 0, 8, _, Prefix),
    atom_concat('0x', Prefix, HexAtom),
    atom_number(HexAtom, Hash),
    max_hash_slots(Slots),
    Slot is Hash mod Slots.

gate(Agent, Capability, Signal, Tokens, Verdict) :-
    (   \+ can_use(Agent, Capability)
    ->  Verdict = reject(no_trust_deed(Agent, Capability))
    ;   shrew_cut(Signal, gate(Agent, Capability), sker_noise)
    ->  Verdict = reject(sker_noise(Signal))
    ;   max_context_tokens(Max),
        \+ ( integer(Tokens), Tokens >= 0, Tokens =< Max )
    ->  Verdict = reject(token_limit_exceeded(Tokens, Max))
    ;   hash_slot(Agent, Capability, Signal, HashSlot),
        Verdict = pass(HashSlot)
    ).

% Demonstration queries with their derived bindings.
% show(Query, Name, Var): print the query with Var shown as Name, then the derived answer.
show(Query, Name, Var) :-
    copy_term(Query-Var, Shown-Var0),
    Var0 = '$VAR'(Name),
    numbervars(Shown, 0, _),
    format("?- ~W.~n", [Shown, [quoted(true), numbervars(true)]]),
    (   call(Query)
    ->  format("   ~w = ~q~n", [Name, Var])
    ;   format("   false~n")
    ).

demo :-
    format("% pass case~n"),
    show(gate(agent_alpha, cap_seal_recursion, sig_heartbeat, 1024, V1), 'Verdict', V1),
    format("% unknown signal~n"),
    show(gate(agent_alpha, cap_seal_recursion, sig_hallucinated, 1024, V2), 'Verdict', V2),
    format("% known noise individual~n"),
    show(shrew_cut(sig_static_burst, none, R1), 'Result', R1),
    format("% proven signal~n"),
    show(shrew_cut(sig_quorum_ack, none, R2), 'Result', R2),
    format("% agent without deed~n"),
    show(gate(agent_gamma, cap_seal_recursion, sig_heartbeat, 1024, V3), 'Verdict', V3),
    format("% deed on a capability not granted~n"),
    show(gate(agent_beta, cap_seal_recursion, sig_heartbeat, 1024, V4), 'Verdict', V4),
    format("% deed whose agent is absent from the anchor~n"),
    show(can_use(agent_ghost, cap_read_mesh), 'Answer', _),
    format("% over-limit tokens~n"),
    show(gate(agent_alpha, cap_read_mesh, sig_merkle_root, 4097, V5), 'Verdict', V5),
    format("% limit boundary~n"),
    show(gate(agent_alpha, cap_read_mesh, sig_merkle_root, 4096, V6), 'Verdict', V6),
    format("% all usable (agent, capability) pairs~n"),
    show(findall(A-C, can_use(A, C), Pairs), 'Pairs', Pairs),
    format("% limits~n"),
    show((max_context_tokens(T), max_hash_slots(S), max_mem_len(M), L = [T, S, M]),
         'Limits', L).
