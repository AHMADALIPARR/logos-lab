// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
// Copyright Ahmad Ali Parr
//
// Verification layer of the tripartite execution lock (OWL 2 DL -> Prolog -> Boogie).
// Limits mirror trust_gate.pl: max_context_tokens/1, max_hash_slots/1, max_mem_len/1.

const max_context_tokens: int;
axiom max_context_tokens == 4096;

const max_hash_slots: int;
axiom max_hash_slots == 16;

const max_mem_len: int;
axiom max_mem_len == 65536;

// Gate verdict codes, in the order trust_gate.pl:gate/5 decides them.
const unique VerdictPass: int;
const unique VerdictNoDeed: int;
const unique VerdictNoise: int;
const unique VerdictOverLimit: int;

// Mirror of gate/5: no deed, then sker_noise, then token limit, else pass.
function GateVerdict(has_deed: bool, proven: bool, toks: int): int;
axiom (forall d: bool, p: bool, t: int ::
  GateVerdict(d, p, t) ==
    (if !d then VerdictNoDeed
     else if !p then VerdictNoise
     else if t < 0 || t > max_context_tokens then VerdictOverLimit
     else VerdictPass));

// Global agent state.
var tokens: int;
var mem_base: int;
var mem_len: int;
var ptr: int;
var offset: int;
var worm_sealed: bool;
var hash_slots: int;      // WORM hashes assigned to the current execution
var slot: int;            // index of the assigned hash slot

// Well-formed memory window and token budget.
function WellFormed(toks: int, base: int, mlen: int): bool {
  0 <= toks && toks <= max_context_tokens &&
  0 <= base && 0 <= mlen && mlen <= max_mem_len
}

// Assign exactly one WORM hash to an execution that has none.
procedure AssignWORMHash(s: int)
  modifies hash_slots, slot;
  requires hash_slots == 0;
  requires 0 <= s && s < max_hash_slots;
  ensures hash_slots == 1;
  ensures slot == s;
{
  hash_slots := hash_slots + 1;
  slot := s;
}

// Model of the HolyC WORM SealRecursion FFI entry: only legal with exactly one hash.
procedure SealRecursion()
  modifies worm_sealed;
  requires hash_slots == 1;
  requires !worm_sealed;
  ensures worm_sealed;
{
  worm_sealed := true;
}

// Deterministic state transition immediately before the FFI handoff.
procedure PrepareFFIHandoff(len: int, s: int)
  modifies hash_slots, slot, worm_sealed, ptr;
  requires WellFormed(tokens, mem_base, mem_len);
  requires tokens <= max_context_tokens;
  requires 0 <= offset;
  requires 0 <= len;
  requires offset + len <= mem_len;
  requires !worm_sealed;
  requires hash_slots == 0;
  requires 0 <= s && s < max_hash_slots;
  ensures hash_slots == 1;
  ensures hash_slots == old(hash_slots) + 1;
  ensures slot == s && 0 <= slot && slot < max_hash_slots;
  ensures !old(worm_sealed) && worm_sealed;
  ensures tokens == old(tokens) && tokens <= max_context_tokens;
  ensures ptr == mem_base + offset;
  ensures mem_base <= ptr;
  ensures ptr + len <= mem_base + mem_len;
  ensures mem_base == old(mem_base) && mem_len == old(mem_len) && offset == old(offset);
{
  call AssignWORMHash(s);
  ptr := mem_base + offset;
  call SealRecursion();
}

// Advance the window offset one cell at a time without leaving the buffer.
procedure WalkWindow(n: int)
  modifies offset;
  requires 0 <= n;
  requires 0 <= offset;
  requires offset + n <= mem_len;
  ensures offset == old(offset) + n;
  ensures 0 <= offset && offset <= mem_len;
{
  var i: int;
  i := 0;
  while (i < n)
    invariant 0 <= i && i <= n;
    invariant offset == old(offset) + i;
    invariant 0 <= offset && offset + (n - i) <= mem_len;
  {
    offset := offset + 1;
    i := i + 1;
  }
}

// Caller: the handoff happens only after the gate verdict is VerdictPass.
procedure GatedHandoff(has_deed: bool, proven: bool, toks: int, len: int, s: int)
    returns (v: int)
  modifies tokens, hash_slots, slot, worm_sealed, ptr;
  requires WellFormed(tokens, mem_base, mem_len);
  requires 0 <= offset && 0 <= len && offset + len <= mem_len;
  requires !worm_sealed && hash_slots == 0;
  requires 0 <= s && s < max_hash_slots;
  ensures v == GateVerdict(has_deed, proven, toks);
  ensures worm_sealed <==> v == VerdictPass;
  ensures v == VerdictPass ==> hash_slots == 1 && tokens == toks && tokens <= max_context_tokens;
  ensures v == VerdictPass ==> ptr == mem_base + offset && ptr + len <= mem_base + mem_len;
  ensures v != VerdictPass ==> hash_slots == 0 && !worm_sealed;
  ensures v != VerdictPass ==> tokens == old(tokens) && ptr == old(ptr) && slot == old(slot);
  ensures mem_base == old(mem_base) && mem_len == old(mem_len) && offset == old(offset);
{
  v := GateVerdict(has_deed, proven, toks);
  if (v == VerdictPass) {
    tokens := toks;
    call PrepareFFIHandoff(len, s);
  }
}

// End to end: walk to the target cell, gate, then hand off.
procedure Dispatch(has_deed: bool, proven: bool, toks: int, skip: int, len: int, s: int)
    returns (v: int)
  modifies tokens, offset, hash_slots, slot, worm_sealed, ptr;
  requires WellFormed(tokens, mem_base, mem_len);
  requires 0 <= offset && 0 <= skip && 0 <= len;
  requires offset + skip + len <= mem_len;
  requires !worm_sealed && hash_slots == 0;
  requires 0 <= s && s < max_hash_slots;
  ensures v == GateVerdict(has_deed, proven, toks);
  ensures worm_sealed <==> v == VerdictPass;
  ensures worm_sealed ==> hash_slots == 1 && tokens <= max_context_tokens;
  ensures worm_sealed ==> mem_base <= ptr && ptr + len <= mem_base + mem_len;
  ensures !worm_sealed ==> hash_slots == 0;
{
  call WalkWindow(skip);
  call v := GatedHandoff(has_deed, proven, toks, len, s);
}
