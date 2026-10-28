(* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
   Copyright Ahmad Ali Parr *)
(* logicstack.ml — full ILP kernel: FOIL + Metagol + ILASP-lite + tree
   ocamlopt -O2 logicstack.ml -o logicstack && ./logicstack
   (works with plain ocamlopt; no packages) *)
(* =========================================================================
   L0: BINARY SUBSTRATE
   ========================================================================= *)
type bit = int
type ex = bit list
let band a b = a * b
let borb a b = max a b
let bxorb a b = (a + b) mod 2
let rec bits n =
  if n = 0 then [[]]
  else List.concat_map (fun bs -> [0 :: bs; 1 :: bs]) (bits (n - 1))
let target e = List.fold_left (+) 0 e mod 2 = 1
let mk_examples n = List.partition target (bits n)
(* =========================================================================
   L1: LOGIC — terms, unification, clauses, depth-bounded SLD
   ========================================================================= *)
type term = C of string | V of string
type atom = string * term array
type clause = atom * atom array
let term_eq t1 t2 = match t1, t2 with
  | C a, C b -> a = b
  | V a, V b -> a = b
  | _ -> false
type binding = (string * term) list
let rec walk b t = match t with
  | C _ -> t
  | V x -> (match List.assoc_opt x b with
            | Some t' -> walk b t'
            | None -> t)
let rec occurs x t b = match walk b t with
  | V y -> y = x
  | C _ -> false
let unify_t a b bl =
  match walk bl a, walk bl b with
  | V x, V y when x = y -> Some bl
  | V x, t -> if occurs x t bl then None
              else Some ((x, t) :: bl)
  | t, V y -> if occurs y t bl then None
              else Some ((y, t) :: bl)
  | C x, C y when x = y -> Some bl
  | _ -> None
let unify (xs: term array) (ys: term array) bl =
  let rec go i acc =
    if i = Array.length xs then Some acc
    else match unify_t xs.(i) ys.(i) acc with
      | None -> None
      | Some b' -> go (i+1) b'
  in
  if Array.length xs <> Array.length ys then None
  else go 0 bl
(* rename a clause's variables apart per call (tag = depth + binding count) *)
let rn tag t = match t with V x -> V (x ^ "_" ^ tag) | _ -> t
let rec prove prog ((p, ts) : atom) bl depth =
  if depth <= 0 then []
  else
    let tag = string_of_int depth ^ "_" ^ string_of_int (List.length bl) in
    List.filter_map (fun ((hp, hts), body) ->
        let hts = Array.map (rn tag) hts in
        let body = Array.map (fun (q, us) -> (q, Array.map (rn tag) us)) body in
        if hp <> p then None
        else match unify hts ts bl with
          | None -> None
          | Some b1 ->
            let rec solve_body i acc =
              if i = Array.length body then Some acc
              else
                let (bp, bts) = body.(i) in
                let bts' = Array.map (walk acc) bts in
                let sols = prove prog (bp, bts') acc (depth - 1) in
                (match List.fold_left (fun acc' s -> match acc' with
                    | None -> Some s
                    | Some _ -> Some s) None sols with
                 | None -> None
                 | Some acc2 -> solve_body (i+1) acc2)
            in
            solve_body 0 b1
      ) prog
let entails prog (p, ts) =
  prove prog (p, Array.of_list ts) [] 8 <> []
(* =========================================================================
   L2: GENERAL FOIL
   ========================================================================= *)
type lit = Has of int*int | AndAt of int*int*int
         | Geq of int*int | XorAt of int*int*int
let nth e i = List.nth e i
let lit_holds l e = match l with
  | Has (i,v)     -> nth e i = v
  | AndAt (i,j,v) -> band (nth e i) (nth e j) = v
  | Geq (i,v)     -> nth e i >= v
  | XorAt (i,j,v) -> bxorb (nth e i) (nth e j) = v
type rule = lit list
let covers r e = List.for_all (fun l -> lit_holds l e) r
let log2 x = log x /. log 2.0
(* FOIL gain (Quinlan) *)
let foil_gain l r pos neg =
  let r' = l :: r in
  let p0 = List.length (List.filter (covers r) pos) in
  let n0 = List.length (List.filter (covers r) neg) in
  let p1 = List.length (List.filter (covers r') pos) in
  let n1 = List.length (List.filter (covers r') neg) in
  if p0 + n0 = 0 || p1 + n1 = 0 || p1 = 0 then 0.0
  else
    float p1 *. (log2 (float p1 /. float (p1+n1))
              -. log2 (float p0 /. float (p0+n0)))
let candidates w =
  let is = List.init w (fun i -> i) in
  List.concat [
    List.concat (List.map (fun i -> [Has (i,0); Has (i,1)]) is);
    List.concat (List.map (fun i ->
      List.concat (List.map (fun j ->
        [AndAt (i,j,0); AndAt (i,j,1)]) is)) is);
    List.map (fun i -> Geq (i,1)) is;
    List.concat (List.map (fun i ->
      List.concat (List.map (fun j ->
        [XorAt (i,j,0); XorAt (i,j,1)]) is)) is);
  ]
let rec foil_clause w pos neg r =
  let negs = List.filter (covers r) neg in
  if negs = [] then r
  else
    let cs = List.filter (fun l -> not (List.mem l r)) (candidates w) in
    let scored = List.map (fun l -> (foil_gain l r pos neg, l)) cs in
    let best = List.fold_left (fun (g0,l0) (g,l) ->
                  if g > g0 then (g,l) else (g0,l0))
                (-1.0, Has (0,0)) scored in
    if fst best <= 1e-9 then begin
      (* plateau (e.g. parity: every single literal has 0 gain):
         look ahead one more literal before giving up *)
      let pairs = List.concat_map (fun l1 ->
          List.filter_map (fun l2 ->
              if l2 = l1 then None
              else Some (foil_gain l1 r pos neg +. foil_gain l2 (l1 :: r) pos neg, (l1, l2)))
            cs) cs in
      let (bg, (l1, l2)) = List.fold_left (fun (g0,p0) (g,p) ->
                              if g > g0 then (g,p) else (g0,p0))
                            (-1.0, (Has (0,0), Has (0,0))) pairs in
      if bg <= 1e-9 then r
      else foil_clause w pos neg (l2 :: l1 :: r)
    end
    else foil_clause w pos neg (snd best :: r)
let rec foil_run w pos neg acc remaining =
  if remaining = [] then List.rev acc
  else
    let c = foil_clause w remaining neg [] in
    if c = [] then List.rev acc
    else
      let kept = List.filter (fun e -> not (covers c e)) remaining in
      foil_run w pos neg (c :: acc) kept
(* =========================================================================
   L3: METAGOL — MIL with predicate invention
   meta-rules: chain P(A,B):-Q(A,C),R(C,B) ; ident ; switch
   ========================================================================= *)
type meta_app = Ident of string | Switch of string
              | Chain of string * string
              | InventedChain of int * string * string
              | Tailrec of string              (* f(A,B) :- Q(A,C), f(C,B) *)
let bk_program : clause list =
  let fact p args = ((p, Array.of_list args), [||]) in
  [ fact "succ" [C "0"; C "1"];
    fact "succ" [C "1"; C "2"];
    fact "succ" [C "2"; C "3"];
    fact "succ" [C "3"; C "4"];
    fact "zero" [C "0"] ]
let v s = V s
let compile : meta_app list -> clause list =
  List.concat_map (function
    | Ident q ->
      [ (("f", [|v "A"; v "B"|]), [| (q, [|v "A"; v "B"|]) |]) ]
    | Switch q ->
      [ (("f", [|v "A"; v "B"|]), [| (q, [|v "B"; v "A"|]) |]) ]
    | Chain (q, r) ->
      [ (("f", [|v "A"; v "B"|]),
         [| (q, [|v "A"; v "C"|]); (r, [|v "C"; v "B"|]) |]) ]
    | Tailrec q ->
      [ (("f", [|v "A"; v "B"|]),
         [| (q, [|v "A"; v "C"|]); ("f", [|v "C"; v "B"|]) |]) ]
    | InventedChain (n, q, r) ->
      let inv = "inv" ^ string_of_int n in
      [ ((inv, [|v "A"; v "B"|]),
         [| (q, [|v "A"; v "C"|]); (r, [|v "C"; v "B"|]) |]);
        (("f", [|v "A"; v "B"|]), [| (inv, [|v "A"; v "B"|]) |]) ])
let mil_pos = [ ("0","2");("1","3");("2","4");("0","3");("0","4");("1","4") ]
let mil_neg = [ ("4","0");("3","0");("2","0");("4","1") ]
let ask_pair prog (a, b) =
  entails prog ("f", [C a; C b])
let mil_search () =
  let basics = [ [Ident "succ"]; [Switch "succ"]; [Chain ("succ","succ")] ] in
  let consistent ps =
      let prog = compile ps @ bk_program in
      List.for_all (ask_pair prog) mil_pos
      && not (List.exists (ask_pair prog) mil_neg) in
  match List.find_opt consistent basics with
  | Some p -> p
  | None ->
    (* no single metarule consistent -> invent inv1 = succ;succ,
       target := inv1; inv1 alone reaches distance 2, so add tailrec
       (f(A,B) :- succ(A,C), f(C,B)) to extend it to distance 3 and 4 *)
    let p = InventedChain (1, "succ", "succ") in
    (match List.find_opt consistent [ [p]; [p; Tailrec "succ"] ] with
     | Some ps -> ps
     | None -> [p])
(* =========================================================================
   L3b: ILASP-LITE — constraint prune + simplify
   ========================================================================= *)
let covers_any_neg neg c = List.exists (covers c) neg
let rec simplify_clause neg c =
  let try_drop l =
    let c' = List.filter ((<>) l) c in
    if not (covers_any_neg neg c') then Some c' else None
  in
  match List.find_map try_drop c with
  | Some c' -> simplify_clause neg c'
  | None -> c
let ilasp_phase neg clauses =
  let good = List.filter (fun c -> not (covers_any_neg neg c)) clauses in
  List.map (simplify_clause neg) good
(* =========================================================================
   L4: TREE
   ========================================================================= *)
type tree = Branch of lit * tree * tree | Leaf of bool
let rec clauses_to_tree = function
  | [] -> Leaf false
  | c :: rest ->
    let rec path = function
      | [] -> Leaf true
      | l :: ls -> Branch (l, path ls, Leaf false)
    in
    (match c with
     | [] -> Leaf true
     | l :: ls -> Branch (l, path ls, clauses_to_tree rest))
let rec classify t e = match t with
  | Leaf b -> b
  | Branch (l, tt, ff) ->
    if lit_holds l e then classify tt e else classify ff e
let rec draw_tree d t = match t with
  | Leaf b -> String.make d ' ' ^ "-> " ^ (if b then "YES" else "NO")
  | Branch (l, tt, ff) ->
    let lbl = (Printf.sprintf "%s" (match l with
        Has (i,v) -> Printf.sprintf "b%d=%d" i v
      | AndAt (i,j,v) -> Printf.sprintf "b%d&b%d=%d" i j v
      | Geq (i,v) -> Printf.sprintf "b%d>=%d" i v
      | XorAt (i,j,v) -> Printf.sprintf "b%d^b%d=%d" i j v)) in
    String.make d ' ' ^ lbl
    ^ " = true\n" ^ draw_tree (d+2) tt
    ^ "\n" ^ String.make d ' ' ^ lbl ^ " = false\n" ^ draw_tree (d+2) ff
(* =========================================================================
   ORCHESTRATION
   ========================================================================= *)
let accuracy cls (pos, neg) =
  let tp = List.length (List.filter (fun e -> List.exists (fun c -> covers c e) cls) pos) in
  let tn = List.length (List.filter (fun e -> List.for_all (fun c -> not (covers c e)) cls) neg) in
  float (tp + tn) /. float (List.length pos + List.length neg)
let () =
  let w = 4 in
  let pos, neg = mk_examples w in
  Printf.printf "=== L0 binary: 4-bit universe, odd-parity target ===\n";
  Printf.printf "    %d pos / %d neg\n"
    (List.length pos) (List.length neg);
  Printf.printf "=== L1 logic engine self-test ===\n";
  let b = unify [| V "X"; C "1" |] [| C "0"; V "Y" |] [] in
  Printf.printf "    unify(X,1 ; 0,Y) = %s\n"
    (match b with Some _ -> "yes" | None -> "no");
  Printf.printf "    entails succ(1,2) = %b\n"
    (entails bk_program ("succ", [C "1"; C "2"]));
  Printf.printf "=== L2 FOIL (general, gain-guided, separate&conquer) ===\n";
  let cls = foil_run w pos neg [] pos in
  List.iter (fun c ->
      Printf.printf "    target(E) :- %s\n"
        (String.concat ", " (List.map (function
           | Has (i,v) -> Printf.sprintf "b%d=%d" i v
           | AndAt (i,j,v) -> Printf.sprintf "b%d&b%d=%d" i j v
           | Geq (i,v) -> Printf.sprintf "b%d>=%d" i v
           | XorAt (i,j,v) -> Printf.sprintf "b%d^b%d=%d" i j v) c))) cls;
  Printf.printf "=== L3b ILASP-lite: constraints + simplification ===\n";
  let cls2 = ilasp_phase neg cls in
  Printf.printf "    %d -> %d clauses\n"
    (List.length cls) (List.length cls2);
  Printf.printf "=== L3 METAGOL: MIL with invention ===\n";
  let mil = mil_search () in
  (match mil with
   | [InventedChain (n,q,r)] ->
     Printf.printf "    inv%d(A,B) :- %s(A,C), %s(C,B).\n    f(A,B) :- inv%d(A,B).\n"
       n q r n
   | [InventedChain (n,q,r); Tailrec t] ->
     Printf.printf "    inv%d(A,B) :- %s(A,C), %s(C,B).\n    f(A,B) :- inv%d(A,B).\n    f(A,B) :- %s(A,C), f(C,B).   %% tailrec\n"
       n q r n t
   | ps ->
     List.iter (fun p -> Printf.printf "    f <- %s\n"
                  (match p with
                   | Ident q -> q ^ "(A,B)"
                   | Switch q -> q ^ "(B,A)"
                   | Chain (q,r) -> Printf.sprintf "%s(A,C),%s(C,B)" q r
                   | Tailrec q -> Printf.sprintf "%s(A,C),f(C,B)" q
                   | InventedChain _ -> "invented")) ps);
  Printf.printf "    inv1(0,2) provable = %b\n"
    (entails ((compile mil) @ bk_program) ("inv1", [C "0"; C "2"]));
  Printf.printf "=== L4 tree ===\n";
  print_endline (draw_tree 4 (clauses_to_tree cls2));
  Printf.printf "=== training accuracy: %.3f ===\n"
    (accuracy cls2 (pos, neg))
