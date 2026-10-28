(* SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
   Copyright Ahmad Ali Parr *)
(* logicstack.ml — FOIL + mini-Metagol + tree
   ocamlfind ocamlopt -package str -linkpkg logicstack.ml -o ls
   (or plain: ocamlopt logicstack.ml -o ls, str-free version below) *)
(* ============ L0: BINARY ============ *)
let band = (land)
let borb = (lor)
let bxor = (lxor)
let bits n =
  let rec go k acc =
    if k = 0 then acc
    else go (k-1) (List.concat_map (fun bs -> [0::bs; 1::bs]) acc)
  in go n [[]]
let target e = List.fold_left (+) 0 e land 1 = 1
let mk_examples n =
  let all = bits n in
  List.partition target all
(* ============ L1: LOGIC ============ *)
type term = C of string | V of string
type atom = string * term list
type clause = atom * atom list
type binding = (string * term) list
let rec subst b t = match t with
  | C _ -> t
  | V x -> (match List.assoc_opt x b with
            | Some t' -> subst b t'
            | None -> t)
let rec unify (xs:term list) (ys:term list) b =
  match xs, ys with
  | [], [] -> Some b
  | x::xr, y::yr ->
    let x', y' = subst b x, subst b y in
    (match x', y' with
     | _ when x' = y' -> unify xr yr b        (* identical after substitution: no self-binding *)
     | V a, V c -> unify xr yr ((a, y')::b)
     | V a, _   -> unify xr yr ((a, y')::b)
     | _,   V c -> unify xr yr ((c, x')::b)
     | C a, C c when a = c -> unify xr yr b
     | _ -> None)
  | _ -> None
let fresh = ref 0
let ren tag t = match t with V x -> V (x ^ "'" ^ string_of_int tag) | c -> c
(* solve a goal list left to right, threading the bindings; clause variables renamed apart per call *)
let rec solve (kb:clause list) goals b depth =
  match goals with
  | [] -> true
  | _ when depth <= 0 -> false
  | (p,args)::rest ->
    let args = List.map (subst b) args in
    List.exists (fun ((h,hargs), body) ->
      if h <> p || List.length hargs <> List.length args then false
      else begin
        incr fresh; let tag = !fresh in
        let hargs = List.map (ren tag) hargs in
        let body = List.map (fun (q,ts) -> (q, List.map (ren tag) ts)) body in
        match unify hargs args b with
        | None -> false
        | Some b1 -> solve kb (body @ rest) b1 (depth-1)
      end) kb
let prove (kb:clause list) (a:atom) b depth = solve kb [a] b depth
(* ============ L2: FOIL ============ *)
type lit = Has of int*int | AndAt of int*int*int | XorAt of int*int*int
let lit_holds l e = match l with
  | Has (i,v)      -> List.nth e i = v
  | AndAt (i,j,v)  -> band (List.nth e i) (List.nth e j) = v
  | XorAt (i,j,v)  -> bxor (List.nth e i) (List.nth e j) = v
let covers rule e = List.for_all (fun l -> lit_holds l e) rule
let entropy p =
  if p <= 0.0 || p >= 1.0 then 0.0
  else -. (p *. log p +. (1.0-.p) *. log (1.0-.p))
let foil_gain ~rule pos neg =
  let tot = List.length pos + List.length neg in
  if tot = 0 then 0.0
  else
    let sub = List.filter (covers rule) (pos @ neg) in
    let sn = List.length sub in
    if sn = 0 then 0.0
    else
      let sp = List.length (List.filter (covers rule) pos) in
      let p0 = float_of_int (List.length pos) /. float_of_int tot in
      let p1 = float_of_int sp /. float_of_int sn in
      entropy p0 -. (float_of_int sn /. float_of_int tot) *. entropy p1
let candidates w =
  (List.concat (List.init w (fun i -> [Has (i,0); Has (i,1)])))
  @ (List.concat (List.init w (fun i ->
      List.concat (List.init (w-i-1) (fun d ->
        [AndAt (i, i+1+d, 0); AndAt (i, i+1+d, 1)])))))
  @ (List.concat (List.init w (fun i ->
      List.concat (List.init (w-i-1) (fun d ->
        [XorAt (i, i+1+d, 0); XorAt (i, i+1+d, 1)])))))
let rec foil w pos neg rule =
  let negs = List.filter (covers rule) neg in
  if negs = [] then rule
  else
    let cands = List.filter (fun l -> not (List.mem l rule)) (candidates w) in
    match cands with
    | [] -> rule
    | _  ->
      let best = List.fold_left
        (fun best l ->
           let g = foil_gain ~rule:(l::rule) pos neg in
           let gb = foil_gain ~rule:(best::rule) pos neg in
           if g > gb then l else best)
        (List.hd cands) (List.tl cands) in
      let prec ls =
        let c = List.length (List.filter (covers ls) pos)
        and n = List.length (List.filter (covers ls) neg) in
        if c + n = 0 then 0.0 else float_of_int c /. float_of_int (c + n) in
      if prec (best::rule) > prec rule then foil w pos neg (best::rule)
      else
        (* plateau (parity: every single literal leaves precision unchanged): look ahead two literals *)
        let pairs = List.concat_map (fun l1 -> List.filter_map
                      (fun l2 -> if l1 = l2 then None else Some [l1;l2]) cands) cands in
        let (bls, _) = List.fold_left (fun (bl,bs) ls ->
            let sc = (prec (ls @ rule), List.length (List.filter (covers (ls @ rule)) pos)) in
            if sc > bs then (ls, sc) else (bl, bs))
          ([], (prec rule, max_int)) pairs in
        (match bls with [] -> rule | ls -> foil w pos neg (ls @ rule))
(* separate & conquer: learn clauses until every positive is covered *)
let foil_all w pos neg =
  let rec loop ps =
    if ps = [] then []
    else
      let r = foil w ps neg [] in
      let ps' = List.filter (fun e -> not (covers r e)) ps in
      if List.length ps' = List.length ps then [] else r :: loop ps'
  in loop pos
(* ============ L3: METAGOL (mini) ============
   meta-chain: P(A,B) :- Q(A,C), R(C,B)
   invented inv1 = next then next *)
let bk : clause list =
  [ (("next",[C"0";C"1"]), []);
    (("next",[C"1";C"2"]), []);
    (("next",[C"2";C"3"]), []);
    (("inv1",[V"A";V"B"]),
     [ ("next",[V"A";V"C"]); ("next",[V"C";V"B"]) ]);
    (* target f: f(A,B):-next(A,B).  f(A,B):-inv1(A,B).  f(A,B):-next(A,C),inv1(C,B). *)
    (("f",[V"A";V"B"]), [ ("next",[V"A";V"B"]) ]);
    (("f",[V"A";V"B"]), [ ("inv1",[V"A";V"B"]) ]);
    (("f",[V"A";V"B"]), [ ("next",[V"A";V"C"]); ("inv1",[V"C";V"B"]) ]) ]
let mil a b = prove bk ("inv1", [C a; C b]) [] 8
let f_holds a b = prove bk ("f", [C a; C b]) [] 24
(* ============ L4: TREE ============ *)
type tree = Node of string * tree list | Leaf of string * bool
let rec rule_to_tree = function
  | []    -> Leaf ("default", true)
  | l::r  -> Node (Printf.sprintf "%s" (match l with
                Has (i,v) -> Printf.sprintf "b%d=%d" i v
              | AndAt (i,j,v) -> Printf.sprintf "b%d&b%d=%d" i j v
              | XorAt (i,j,v) -> Printf.sprintf "b%d^b%d=%d" i j v),
             [rule_to_tree r])
let rec draw depth t = match t with
  | Leaf (s,v) ->
    Printf.printf "%s-> %s = %b\n" (String.make depth ' ') s v
  | Node (s, kids) ->
    Printf.printf "%s%s\n" (String.make depth ' ') s;
    List.iter (draw (depth+2)) kids
let () =
  let w = 4 in
  let pos, neg = mk_examples w in
  Printf.printf "L0: %d pos / %d neg\n"
    (List.length pos) (List.length neg);
  Printf.printf "L1: next(0,1)=%b inv1(0,2)=%b inv1(2,0)=%b\n"
    (prove bk ("next",[C"0";C"1"]) [] 4)
    (mil "0" "2") (mil "2" "0");
  let rules = foil_all w pos neg in
  Printf.printf "L2: FOIL rules (%d clauses):\n" (List.length rules);
  List.iter (fun rule ->
    Printf.printf "     target(E) :- ";
    List.iter (fun l -> match l with
      | Has (i,v) -> Printf.printf "b%d=%d " i v
      | AndAt (i,j,v) -> Printf.printf "b%d&b%d=%d " i j v
      | XorAt (i,j,v) -> Printf.printf "b%d^b%d=%d " i j v) (List.rev rule);
    print_newline ()) rules;
  let mp = [("0","1");("1","2");("2","3");("0","2");("0","3");("1","3")]
  and mn = [("3","0");("2","0");("3","1")] in
  let cnt l = List.length (List.filter (fun (a,b) -> f_holds a b) l) in
  Printf.printf "L3: inv1 invented via meta-chain\n";
  Printf.printf "     f(A,B) :- next(A,B).  f(A,B) :- inv1(A,B).  f(A,B) :- next(A,C), inv1(C,B).\n";
  Printf.printf "     f covers %d/6 pos, %d/3 neg\n" (cnt mp) (cnt mn);
  Printf.printf "L4:\n";
  List.iter (fun rule -> draw 2 (rule_to_tree (List.rev rule))) rules;
  let all = pos @ neg in
  let ok = List.length (List.filter (fun e ->
             List.exists (fun r -> covers r e) rules = target e) all) in
  Printf.printf "training accuracy: %.3f\n" (float_of_int ok /. float_of_int (List.length all))
