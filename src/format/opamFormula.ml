(**************************************************************************)
(*                                                                        *)
(*    Copyright 2012-2015 OCamlPro                                        *)
(*    Copyright 2012 INRIA                                                *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

type relop = [`Eq|`Neq|`Geq|`Gt|`Leq|`Lt]

let neg_relop = function
  | `Eq -> `Neq
  | `Neq -> `Eq
  | `Geq -> `Lt
  | `Gt -> `Leq
  | `Leq -> `Gt
  | `Lt -> `Geq

type version_constraint = relop * OpamPackage.Version.t

type atom = OpamPackage.Name.t * version_constraint option

let string_of_atom = function
  | n, None       -> OpamPackage.Name.to_string n
  | n, Some (r,c) ->
    Printf.sprintf "%s (%s %s)"
      (OpamPackage.Name.to_string n)
      (OpamPrinter.relop r)
      (OpamPackage.Version.to_string c)

let short_string_of_atom = function
  | n, None       -> OpamPackage.Name.to_string n
  | n, Some (`Eq,c) ->
    Printf.sprintf "%s.%s"
      (OpamPackage.Name.to_string n)
      (OpamPackage.Version.to_string c)
  | n, Some (r,c) ->
    Printf.sprintf "%s%s%s"
      (OpamPackage.Name.to_string n)
      (OpamPrinter.relop r)
      (OpamPackage.Version.to_string c)

let string_of_atoms atoms =
  OpamStd.List.concat_map " & " short_string_of_atom atoms

type 'a conjunction = 'a list

let string_of_conjunction string_of_atom c =
  Printf.sprintf "(%s)" (OpamStd.List.concat_map " & " string_of_atom c)

type 'a disjunction = 'a list

let string_of_disjunction string_of_atom c =
  Printf.sprintf "(%s)" (OpamStd.List.concat_map " | " string_of_atom c)

type 'a cnf = 'a list list

let string_of_cnf string_of_atom cnf =
  let string_of_clause c =
    Printf.sprintf "(%s)" (OpamStd.List.concat_map " | " string_of_atom c) in
  Printf.sprintf "(%s)" (OpamStd.List.concat_map " & " string_of_clause cnf)

type 'a dnf = 'a list list

let string_of_dnf string_of_atom cnf =
  let string_of_clause c =
    Printf.sprintf "(%s)" (OpamStd.List.concat_map " & " string_of_atom c) in
  Printf.sprintf "(%s)" (OpamStd.List.concat_map " | " string_of_clause cnf)

type 'a formula =
  | Empty
  | Atom of 'a
  | Block of 'a formula
  | And of 'a formula * 'a formula
  | Or of 'a formula * 'a formula

let make_and a b = match a, b with
  | Empty, r | r, Empty -> r
  | a, b -> And (a, b)

let make_or a b = match a, b with
  | Empty, r | r, Empty -> r (* we're not assuming Empty is true *)
  | a, b -> Or (a, b)

let string_of_formula string_of_a f =
  let rec aux ?(in_and=false) f =
    let paren_if ?(cond=false) s =
      if cond || OpamFormatConfig.(!r.all_parens)
      then Printf.sprintf "(%s)" s
      else s
    in
    match f with
    | Empty    -> "0"
    | Atom a   -> paren_if (string_of_a a)
    | Block x  -> Printf.sprintf "(%s)" (aux x)
    | And(x,y) ->
      paren_if
        (Printf.sprintf "%s & %s"
           (aux ~in_and:true x) (aux ~in_and:true y))
    | Or(x,y)  ->
      paren_if ~cond:in_and
        (Printf.sprintf "%s | %s" (aux x) (aux y))
  in
  aux f

let rec map f = function
  | Empty    -> Empty
  | Atom x   -> f x
  | And(x,y) -> make_and (map f x) (map f y)
  | Or(x,y)  -> make_or (map f x) (map f y)
  | Block x  ->
    match map f x with
    | Empty -> Empty
    | x -> Block x

(* Maps top-down *)
let rec map_formula f t =
  let t = f t in
  match t with
  | Block x  -> Block (map_formula f x)
  | And(x,y) -> make_and (map_formula f x) (map_formula f y)
  | Or(x,y)  -> make_or (map_formula f x) (map_formula f y)
  | x -> x

let neg neg_atom =
  map_formula
    (function
      | And(x,y) -> Or(x,y)
      | Or(x,y) -> And(x,y)
      | Atom x -> Atom (neg_atom x)
      | x -> x)

let rec iter f = function
  | Empty    -> ()
  | Atom x   -> f x
  | Block x  -> iter f x
  | And(x,y) -> iter f x; iter f y
  | Or(x,y)  -> iter f x; iter f y

let rec fold_left f i = function
  | Empty    -> i
  | Atom x   -> f i x
  | Block x  -> fold_left f i x
  | And(x,y) -> fold_left f (fold_left f i x) y
  | Or(x,y)  -> fold_left f (fold_left f i x) y

type version_formula = version_constraint formula

type t = (OpamPackage.Name.t * version_formula) formula

let rec eval atom = function
  | Empty    -> true
  | Atom x   -> atom x
  | Block x  -> eval atom x
  | And(x,y) -> eval atom x && eval atom y
  | Or(x,y)  -> eval atom x || eval atom y

let rec partial_eval atom = function
  | Empty -> `Formula Empty
  | Atom x -> atom x
  | And(x,y) ->
    (match partial_eval atom x, partial_eval atom y with
     | `False, _ | _, `False -> `False
     | `True, f | f, `True -> f
     | `Formula x, `Formula y -> `Formula (And (x,y)))
  | Or(x,y) ->
    (match partial_eval atom x, partial_eval atom y with
     | `True, _ | _, `True -> `True
     | `False, f | f, `False -> f
     | `Formula x, `Formula y -> `Formula (Or (x,y)))
  | Block x -> partial_eval atom x

let check_relop relop c = match relop with
  | `Eq  -> c =  0
  | `Neq -> c <> 0
  | `Geq -> c >= 0
  | `Gt  -> c >  0
  | `Leq -> c <= 0
  | `Lt  -> c <  0

let eval_relop relop v1 v2 =
  check_relop relop (OpamPackage.Version.compare v1 v2)

let check_version_formula f v =
  eval (fun (relop, vref) -> eval_relop relop v vref) f

let check (name,cstr) package =
  name = OpamPackage.name package &&
  match cstr with
  | None -> true
  | Some (relop, v) -> eval_relop relop (OpamPackage.version package) v

let packages_of_atoms pkgset atoms =
  (* Conjunction for constraints over the same name, but disjunction on the
     package names *)
  let by_name =
    List.fold_left (fun acc (n,_ as atom) ->
        OpamPackage.Name.Map.update n (fun a -> atom::a) [] acc)
      OpamPackage.Name.Map.empty atoms
  in
  OpamPackage.Name.Map.fold (fun name atoms acc ->
      OpamPackage.Set.union acc @@
      OpamPackage.Set.filter
        (fun nv -> List.for_all (fun a -> check a nv) atoms)
        (OpamPackage.packages_of_name pkgset name))
    by_name OpamPackage.Set.empty

let to_string t =
  let string_of_constraint (relop, version) =
    Printf.sprintf "%s %s" (OpamPrinter.relop relop)
      (OpamPackage.Version.to_string version) in
  let string_of_pkg = function
    | n, Empty -> OpamPackage.Name.to_string n
    | n, (Atom _ as c) ->
      Printf.sprintf "%s %s"
        (OpamPackage.Name.to_string n)
        (string_of_formula string_of_constraint c)
    | n, c ->
      Printf.sprintf "%s (%s)"
        (OpamPackage.Name.to_string n)
        (string_of_formula string_of_constraint c) in
  string_of_formula string_of_pkg t

(* convert a formula to a CNF *)
let cnf_of_formula t =
  let rec mk_left x y = match y with
    | Block y   -> mk_left x y
    | And (a,b) -> And (mk_left x a, mk_left x b)
    | Empty     -> x
    | _         -> Or (x,y) in
  let rec mk_right x y = match x with
    | Block x   -> mk_right x y
    | And (a,b) -> And (mk_right a y, mk_right b y)
    | Empty     -> y
    | _         -> mk_left x y in
  let rec mk = function
    | Empty     -> Empty
    | Block x   -> mk x
    | Atom x    -> Atom x
    | And (x,y) -> And (mk x, mk y)
    | Or (x,y)  -> mk_right (mk x) (mk y) in
  mk t

(* convert a formula to DNF *)
let dnf_of_formula t =
  let rec mk_left x y = match y with
    | Block y  -> mk_left x y
    | Or (a,b) -> Or (mk_left x a, mk_left x b)
    | _        -> And (x,y) in
  let rec mk_right x y = match x with
    | Block x  -> mk_right x y
    | Or (a,b) -> Or (mk_right a y, mk_right b y)
    | _        -> mk_left x y in
  let rec mk = function
    | Empty     -> Empty
    | Block x   -> mk x
    | Atom x    -> Atom x
    | Or (x,y)  -> Or (mk x, mk y)
    | And (x,y) -> mk_right (mk x) (mk y) in
  mk t

let verifies f nv =
  let name_formula =
    map (fun ((n, _) as a) -> if n = OpamPackage.name nv then Atom a else Empty)
      (dnf_of_formula f)
  in
  name_formula <> Empty &&
  eval (fun (_name, cstr) ->
      check_version_formula cstr (OpamPackage.version nv))
    name_formula

let packages pkgset f =
  let names =
    fold_left (fun acc (name, _) ->
        OpamPackage.Name.Set.add name acc)
      OpamPackage.Name.Set.empty f
  in
  (* dnf allows us to transform the formula into a union of intervals, where
     ignoring atoms for different package names works. *)
  let dnf = dnf_of_formula f in
  OpamPackage.Name.Set.fold (fun name acc ->
      (* Ignore conjunctions where [name] doesn't appear *)
      let name_formula =
        map (fun ((n, _) as a) -> if n = name then Atom a else Empty) dnf
      in
      OpamPackage.Set.union acc @@
      OpamPackage.Set.filter (fun nv ->
          let v = OpamPackage.version nv in
          eval (fun (_name, cstr) -> check_version_formula cstr v)
            name_formula)
        (OpamPackage.packages_of_name pkgset name))
    names OpamPackage.Set.empty

(* Convert a t an atom formula *)
let to_atom_formula (t:t): atom formula =
  let atom (r,v) = Atom (r, v) in
  let atoms (x, c) =
    match cnf_of_formula (map atom c) with
    | Empty -> Atom (x, None)
    | cs    -> map (fun c -> Atom (x, Some c)) cs in
  map atoms t

(* Convert an atom formula to a t-formula *)
let of_atom_formula (a:atom formula): t =
  let atom (n, v) =
    match v with
    | None       -> Atom (n, Empty)
    | Some (r,v) -> Atom (n, Atom (r,v)) in
  map atom a

(* Convert a formula to CNF *)
let to_cnf (t : t) =
  let rec or_formula = function
    | Atom (x,None)      -> [x, None]
    | Atom (x,Some(r,v)) -> [x, Some(r,v)]
    | Or(x,y)            -> or_formula x @ or_formula y
    | Empty
    | Block _
    | And _      -> assert false in
  let rec aux t = match t with
    | Empty    -> []
    | Block _  -> assert false
    | Atom _
    | Or _     -> [or_formula t]
    | And(x,y) -> aux x @ aux y in
  aux (cnf_of_formula (to_atom_formula t))

(* Convert a formula to DNF *)
let to_dnf t =
  let rec and_formula = function
    | Atom (x,None)      -> [x, None]
    | Atom (x,Some(r,v)) -> [x, Some(r,v)]
    | And(x,y)           -> and_formula x @ and_formula y
    | Empty
    | Block _
    | Or _      -> assert false in
  let rec aux t = match t with
    | Empty   -> []
    | Block _ -> assert false
    | Atom _
    | And _   -> [and_formula t]
    | Or(x,y) -> aux x @ aux y in
  aux (dnf_of_formula (to_atom_formula t))

let to_conjunction t =
  match to_dnf t with
  | []  -> []
  | [x] -> x
  | _   ->
    failwith (Printf.sprintf "%s is not a valid conjunction" (to_string t))

let ands l = List.fold_left make_and Empty l

let rec ands_to_list = function
  | Empty -> []
  | And (e,f) | Block (And (e,f)) -> ands_to_list e @ ands_to_list f
  | x -> [x]

let of_conjunction c =
  of_atom_formula (ands (List.rev_map (fun x -> Atom x) c))

let to_disjunction t =
  match to_cnf t with
  | []  -> []
  | [x] -> x
  | _   ->
    failwith (Printf.sprintf "%s is not a valid disjunction" (to_string t))

let ors l = List.fold_left make_or Empty l

let rec ors_to_list = function
  | Empty -> []
  | Or (e,f) | Block (Or (e,f)) -> ors_to_list e @ ors_to_list f
  | x -> [x]

let of_disjunction d =
  of_atom_formula (ors (List.rev_map (fun x -> Atom x) d))

let atoms t =
  fold_left (fun accu x -> x::accu) [] (to_atom_formula t)

let get_disjunction_formula version_set cstr =
  List.map (fun ff ->
      match ands_to_list ff with
      | [] -> assert false
      | [Atom _] as at -> at
      | _ ->
        OpamPackage.Version.Set.filter (check_version_formula ff) version_set |>
        OpamPackage.Version.Set.elements |>
        List.map (fun v -> Atom (`Eq, v)))
    (ors_to_list cstr) |>
  List.flatten

let set_to_disjunction set t =
  List.map (function
      | And _ ->
        failwith (Printf.sprintf "%s is not a valid disjunction" (to_string t))
      | Or _ | Block _ | Empty -> assert false
      | Atom (name, Empty) -> [name, None]
      | Atom (name, cstr) ->
        get_disjunction_formula
          (OpamPackage.versions_of_name set name)
          cstr |>
        List.map (function
            | Atom (relop, v) -> name, Some (relop, v)
            | _ -> assert false))
    (ors_to_list t) |>
  List.flatten

let simplify_ineq_formula vcomp (get_ineq, make_ineq) f0 =
  (* originally backported from OWS/WeatherReasons *)
  let vmin a b = if vcomp a b <= 0 then a else b in
  let vmax a b = if vcomp a b >= 0 then a else b in
  let mk ineq = `Reduced (make_ineq ineq) in
  let and_cstrs c1 c2 =
    let ifc a op b r = if op (vcomp a b) 0 then mk r else `False in
    let ifp a op b r = if op (vcomp a b) 0 then mk r else `Nred in
    match get_ineq c1, get_ineq c2 with
    | (`Gt, a), (`Gt, b)                      -> mk (`Gt, vmax a b)
    | (`Geq,a), (`Geq,b)                      -> mk (`Geq,vmax a b)
    | (`Gt, a), (`Geq,b) | (`Geq,b), (`Gt, a) ->
      if vcomp a b >= 0 then mk (`Gt, a) else mk (`Geq, b)
    | (`Lt, a), (`Lt, b) -> mk (`Lt, vmin a b)
    | (`Leq,a), (`Leq,b) -> mk (`Leq, vmin a b)
    | (`Lt, a), (`Leq,b) | (`Leq,b), (`Lt, a) ->
      if vcomp a b <= 0 then mk (`Lt, a) else mk (`Leq,b)
    | (`Geq,a), (`Eq, b) | (`Eq, b), (`Geq,a) -> ifc a (<=) b (`Eq, b)
    | (`Gt, a), (`Eq, b) | (`Eq, b), (`Gt, a) -> ifc a (< ) b (`Eq, b)
    | (`Leq,a), (`Eq, b) | (`Eq, b), (`Leq,a) -> ifc a (>=) b (`Eq, b)
    | (`Lt, a), (`Eq, b) | (`Eq, b), (`Lt, a) -> ifc a (> ) b (`Eq, b)
    | (`Geq,a), (`Neq,b) | (`Neq,b), (`Geq,a) -> ifp a (> ) b (`Geq,a)
    | (`Gt, a), (`Neq,b) | (`Neq,b), (`Gt, a) -> ifp a (>=) b (`Gt, a)
    | (`Leq,a), (`Neq,b) | (`Neq,b), (`Leq,a) -> ifp a (< ) b (`Leq,a)
    | (`Lt, a), (`Neq,b) | (`Neq,b), (`Lt, a) -> ifp a (<=) b (`Lt, a)
    | (`Eq, a), (`Eq, b)                      -> ifc a (= ) b (`Eq, a)
    | (`Neq,a), (`Neq,b)                      -> ifp a (= ) b (`Neq,a)
    | (`Eq, a), (`Neq,b) | (`Neq,b), (`Eq, a) -> ifc a (<>) b (`Eq, a)
    | (`Geq,a), (`Leq,b) | (`Leq,b), (`Geq,a) ->
      let c = vcomp a b in
      if c = 0 then mk (`Eq, a) else
      if c < 0 then `Nred else `False
    | (`Gt, a), (`Lt, b) | (`Lt, b), (`Gt, a)
    | (`Gt, a), (`Leq,b) | (`Leq,b), (`Gt, a)
    | (`Geq,a), (`Lt, b) | (`Lt, b), (`Geq,a) ->
      if vcomp a b < 0 then `Nred else `False
  in
  let or_cstrs c1 c2 =
    let ifa a op b r = if op (vcomp a b) 0 then mk r else `True in
    let ifp a op b r = if op (vcomp a b) 0 then mk r else `Nred in
    match get_ineq c1, get_ineq c2 with
    | (`Gt, a), (`Gt, b) -> mk (`Gt, vmin a b)
    | (`Geq,a), (`Geq,b) -> mk (`Geq, vmin a b)
    | (`Gt, a), (`Geq,b) | (`Geq,b), (`Gt, a) ->
      if vcomp a b < 0 then mk (`Gt, a) else mk (`Geq,b)
    | (`Lt, a), (`Lt, b) -> mk (`Lt, vmax a b)
    | (`Leq,a), (`Leq,b) -> mk (`Leq,vmax a b)
    | (`Lt, a), (`Leq,b) | (`Leq,b), (`Lt, a) ->
      if vcomp a b > 0 then mk (`Lt, a) else mk (`Leq,b)
    | (`Geq,a), (`Eq, b) | (`Eq, b), (`Geq,a) -> ifp a (<=) b (`Geq,a)
    | (`Gt, a), (`Eq, b) | (`Eq, b), (`Gt, a) -> ifp a (< ) b (`Gt, a)
    | (`Leq,a), (`Eq, b) | (`Eq, b), (`Leq,a) -> ifp a (>=) b (`Leq,a)
    | (`Lt, a), (`Eq, b) | (`Eq, b), (`Lt, a) -> ifp a (> ) b (`Lt, a)
    | (`Geq,a), (`Neq,b) | (`Neq,b), (`Geq,a) -> ifa a (> ) b (`Neq,b)
    | (`Gt, a), (`Neq,b) | (`Neq,b), (`Gt, a) -> ifa a (>=) b (`Neq,b)
    | (`Leq,a), (`Neq,b) | (`Neq,b), (`Leq,a) -> ifa a (< ) b (`Neq,b)
    | (`Lt, a), (`Neq,b) | (`Neq,b), (`Lt, a) -> ifa a (<=) b (`Neq,b)
    | (`Eq, a), (`Eq, b)                      -> ifp a (= ) b (`Eq, a)
    | (`Neq,a), (`Neq,b)                      -> ifa a (= ) b (`Neq,a)
    | (`Eq, a), (`Neq,b) | (`Neq,b), (`Eq, a) -> ifa a (<>) b (`Neq,b)
    | (`Gt, a), (`Lt, b) | (`Lt, b), (`Gt, a) ->
      let c = vcomp a b in
      if c = 0 then mk (`Neq,a) else
      if c < 0 then `True else `Nred
    | (`Geq,a), (`Leq,b) | (`Leq,b), (`Geq,a)
    | (`Geq,a), (`Lt, b) | (`Lt, b), (`Geq,a)
    | (`Gt, a), (`Leq,b) | (`Leq,b), (`Gt, a) ->
      if vcomp a b <= 0 then `True else `Nred
  in
  let rec simpl_conj_and acc a conj = match conj with
    | [] -> Some (a, acc)
    | b::r -> match and_cstrs a b with
      | `False -> None
      | `Nred -> simpl_conj_and (b::acc) a r
      | `Reduced c ->
        match simpl_conj_and [] c acc with
        | None -> None
        | Some (c, acc) -> simpl_conj_and acc c r
  in
  let rec simpl_conj acc = function
    | [] -> Some acc
    | a :: r ->
      match simpl_conj_and [] a r with
      | None -> None
      | Some (b, rem) -> simpl_conj (b::acc) rem
  in
  let len2 = List.fold_left (List.fold_left (fun x l -> x + List.length l)) 0 in
  let simpl_cnf_or cnf1 cnf2 =
    try
      let maxlen = len2 cnf1 + len2 cnf2 in
      let _len, simpl, nsimpl =
        List.fold_left (fun acc disj_a ->
            List.fold_left (fun (len,simpl,nsimpl) disj_b ->
                if len > maxlen then raise Exit
                else
                match simpl_disj [] disj_a disj_b with
                | None -> acc
                
                simpl (acc & d)
                len + List.length d, 

                (* a and b are now disjunctions; simplify the junction *)
                  let disj = simpl_disj_or a b in
                  List.length disj, disj


 match or_cstrs a b with
                  | `True -> len, simpl, nsimpl
                  | `Nred -> len + 2, simpl, ([a;b] :: nsimpl)
                  | `Reduced c ->
                    match simpl_conj_and [] c simpl with
                    | Some (c, simpl) -> len + 1, c::simpl, nsimpl
                    | None -> assert false)
              acc conj2)
          (0,[],[]) conj1
      in
      match simpl, nsimpl with
      | [], [] -> `True
      | simpl, [] -> `Conj simpl
      | simpl, nsimpl -> `Cnf (List.map (fun x -> [x]) simpl @ nsimpl)
    with Exit -> `Nred
  in


  let simpl_conj_or conj1 conj2 =
    try
      let maxlen = List.length conj1 + List.length conj2 in
      let _len, simpl, nsimpl =
        List.fold_left (fun acc a ->
            List.fold_left (fun (len,simpl,nsimpl) b ->
                if len > maxlen then raise Exit
                else match or_cstrs a b with
                  | `True -> len, simpl, nsimpl
                  | `Nred -> len + 2, simpl, ([a;b] :: nsimpl)
                  | `Reduced c ->
                    match simpl_conj_and [] c simpl with
                    | Some (c, simpl) -> len + 1, c::simpl, nsimpl
                    | None -> assert false)
              acc conj2)
          (0,[],[]) conj1
      in
      match simpl, nsimpl with
      | [], [] -> `True
      | simpl, [] -> `Conj simpl
      | simpl, nsimpl -> `Cnf (List.map (fun x -> [x]) simpl @ nsimpl)
    with Exit -> `Nred
  in
  let rec simpl_dnf_or acc conj dnf = match dnf with
    | [] -> Some (`Conj conj, acc)
    | conj1 :: dnf ->
      match simpl_conj_or conj conj1 with
      | `Nred -> simpl_dnf_or (conj1 :: acc) conj dnf
      | `True -> None
      | `Conj c -> (match simpl_dnf_or [] c acc with
          | None -> None
          | Some (`Conj conj, acc) ->
            simpl_dnf_or acc conj dnf)
      | `Cnf cnf ->
        match simpl_dnf_or (conj1 :: acc) conj dnf with
        | None -> None
        | Some (`Conj _, _) as t -> t
        | Some (`Cnf cnf1, _) as t ->
          let len =
            List.fold_left (List.fold_left (fun x l -> x + List.length l)) 0
          in
          if len cnf1 < len cnf then t
          else Some (`Cnf cnf, List.rev_append acc dnf)
  in
  let rec simpl_dnf acc_dnf acc_cnf = function
    | [] -> Some (acc_dnf, acc_cnf)
    | conj :: dnf ->
      match simpl_dnf_or [] [] conj dnf with
      | None -> []
      | conj, dnf, cnf -> simpl_dnf (dnf::acc_dnf) (cnf::acc_cnf)

  let rec simpl_dnf (acc_conj, acc_cnf) = function
    | [] -> acc
    | conj :: dnf ->
      let rec aux = function
        | [] -> 
        | conj1 :: dnf ->
          match simpl_conj_or conj conj1 with
          | `True -> `True
          | `Conj c -> simpl_dnf (



  let rec simpl_dnf_or acc dnf conj = match dnf with
    | [] -> `Nred
    | conj1::dnf -> match simpl_conj_or conj conj1 with
      | `True -> `True
      | `Conj c -> `Dnf_or_Cnf (List.rev_append acc (c :: dnf), [])
      | `Nred -> simpl_dnf_or (conj1::acc) r conj
      | `Cnf cnf ->
        match simpl_dnf_or (conj1::acc) dnf conj with
        | (`True | `Dnf_or_Cnf (_, [])) as t -> t
        | `Nred -> `Dnf_or_Cnf (List.rev_append acc dnf, cnf)
        | `Dnf_or_Cnf (_, cnf1) as t ->
          let len =
            List.fold_left (List.fold_left (fun x l -> x + List.length l)) 0
          in
          if len cnf1 < len cnf then t
          else `Dnf_or_Cnf (List.rev_append acc dnf, cnf)
  in
  let simpl_dnf =
    List.fold_left (fun acc conj ->
        match acc with
        | `True -> `True
        | `Dnf_or_Cnf (dnf, cnf) ->
          match simpl_dnf_or [] dnf conj with
          | `Nred -> `Dnf_or_Cnf (conj::dnf, cnf)
          | `True -> `True
          | `Dnf d1 -> `Dnf (d1 @ d)
          | `Dnf_or_Cnf (d1, cnf) -> `Dnf_or_Cnf )
      (`Dnf [])
  in
  (* Using a dnf ensures we detect conflicting constraints *)
  let dnf = dnf_of_formula f0 in
  let dnf =
    OpamStd.List.filter_map (fun conj ->
        match simpl_conj conj with
        | `False -> None
        | `Conj c -> Some c)
      dnf
  in
  if dnf = [] then None else
  (* let disj = List.sort (fun l1 l2 -> List.length l1 - List.length l2) disj in *)
    match simpl_dnf dnf with
      | `True -> Some Empty
      | `Dnf d ->
        (* todo: Sort by v *)
        Some (ors (List.map ands d))

let simpl = simplify_ineq_formula (fun a b -> a - b) ((fun x -> x), (fun x -> x));;

let print = OpamStd.Option.to_string ~none:"false" (string_of_formula (fun (op, i) -> OpamPrinter.relop op ^ string_of_int i));;

let f1, f2, f3 =
  let a c x = Atom ((c :> relop), x) in
  let (&) a b = And (a, b) in
  let (+) a b = Or (a, b) in
  (a `Gt 1 & a `Lt 2) + (a `Gt 3 & a `Lt 4) + ((a `Gt 9 + (a `Gt 7 & a `Lt 8)) & a `Lt 12),
  ((a `Gt 0 & a `Lt 1) + (a `Gt 3 & a `Lt 5)) & (a `Gt 2 & a `Lt 4),
  (((a `Gt 0 & a `Lt 1) + (a `Gt 3 & a `Lt 5)) & (a `Gt 2)) + (a `Lt 42)

let s1 = print (Some f3)
let s2 = print (simpl f3)



;;
let simplify_version_formula f =
  simplify_ineq_formula OpamPackage.Version.compare
    ((fun c -> c), (fun c -> c)) f

let simplify_version_set set f =
  let module S = OpamPackage.Version.Set in
  if S.is_empty set then Some Empty else
  let set = fold_left (fun set (_relop, v) -> S.add v set) set f in
  let vmin = S.min_elt set in
  S.fold (fun version acc ->
      if check_version_formula f version
      then match acc with
        | Empty | Atom (`Geq, _) | Or (_, Atom (`Geq, _)) -> acc
        | Atom (`Eq, vl) -> Atom (`Geq, vl)
        | Or (f1, Atom (`Eq, vl)) -> Or (f1, Atom (`Geq, vl))
        | _ -> make_or acc (Atom (`Eq, version))
      else match acc with
        | Atom ((`Lt|`Eq), _)
        | And (_, Atom ((`Lt|`Eq), _))
        | Or (_, (And (_, Atom (`Lt, _))))
          -> acc
        | Or (f1, (Atom ((`Eq|`Geq), _) as atl))
          -> Or (f1, And (atl, (Atom (`Lt, version))))
        | _ -> make_and acc (Atom (`Lt, version)))
    set Empty
  |> function
  | Atom (`Lt, v) when v = vmin -> None
  | f1 ->
    let f =
      map_formula (function
          | And (Atom (`Eq, _) as a1, Atom (`Lt, _)) -> a1
          | Atom (`Lt, v) when v = vmin -> Empty
          | f -> f)
        f1
    in
    Some f

type 'a ext_package_formula =
  (OpamPackage.Name.t * ('a * version_formula)) formula

let formula_of_extended ~filter =
  map (fun (n, (kws,formula)) -> if filter kws then Atom (n, formula) else Empty)

let reduce_extended ~filter =
  map (fun (n, (kws, formula)) ->
      let kws =
        List.fold_left (fun acc kw ->
            match acc with
            | None -> None
            | Some kws -> match filter kw with
              | Some true -> acc
              | Some false -> None
              | None -> Some (kw::kws))
          (Some []) (List.rev kws)
      in
      match kws with
      | None -> Empty
      | Some kws -> Atom (n, (kws, formula)))
