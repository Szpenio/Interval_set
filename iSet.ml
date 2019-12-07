(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint.
*)

(** Problem: Modyfikacja drzew **)
(** Author: Antoni Koszowski **)
(** Reviewer: Jan Olszewski **)

(** type representing set - AVL trees **)
type t =
  | Empty
  | Node of t * (int * int) * t * int * int

(** the empty set **)
let empty = Empty

(** returns [true] if the set [s] is empty **)
let is_empty s =
  s = Empty

(** compares interval k2 with k1 **)
let cmp (k2ran_l, k2ran_r) (k1ran_l, k1ran_r) =
  if k2ran_r < k1ran_r && k2ran_l < k1ran_l then -1 else
  if k2ran_r <= k1ran_r && k2ran_l >= k1ran_l then 0 else 1

let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0

let num_el = function
  | Node (_, _, _, _, n) -> n
  | Empty -> 0

let len x =
  snd x - fst x + 1

(** creates node combined from subtress [l] [r] with interval [k] as node value **)
let make l k r = Node (l, k, r, max (height l) (height r) + 1, num_el l + num_el r + len k)

(** balances tree - maintains AVL trees property **)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
      if height ll >= height lr then make ll lk (make lr k r)
      else
        (match lr with
         | Node (lrl, lrk, lrr, _, _) ->
           make (make ll lk lrl) lrk (make lrr k r)
         | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
      if height rr >= height rl then make (make l k rl) rk rr
      else
        (match rl with
         | Node (rll, rlk, rlr, _, _) ->
           make (make l k rll) rlk (make rlr rk rr)
         | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1, num_el l + num_el r + len k)

(** returns/ deletes min_elt from the given set **)
let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "ISet.remove_min_elt"

(** returns/ deletes max_elt from the given set **)
let rec max_elt = function
  | Node (_, k, Empty, _, _) -> k
  | Node (_, _ , r, _, _) -> max_elt r
  | Empty -> raise Not_found

let rec remove_max_elt = function
  | Node (l, _, Empty, _, _) -> l
  | Node (l, k, r, _, _) -> bal l k (remove_max_elt r)
  | Empty -> invalid_arg "ISet.remove_max_elt"

(** merges left and right subtrees of the given node **)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
    let k = min_elt t2 in
    bal t1 k (remove_min_elt t2)

(** adds interval to AVL tree, assuming that all intervals are separated **)
let rec add_one x = function
  | Node (l, k, r, h, _) ->
    let c = cmp x k in
    if c < 0 then
      let poml = add_one x l in
      bal poml k r
    else
      let pomr = add_one x r in
      bal l k pomr
  | Empty -> Node (Empty, x, Empty, 1, len x)

(** joins given trees, maintaining on every depth AVL trees property **)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_one v r
  | (_, Empty) -> add_one v l
  | (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
    if lh > rh + 2 then bal ll lv (join lr v r) else
    if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

(** divides tree into subtrees containig lower/ higher valuse than [n]
    returns [true] if the given tree contains the value [n]            **)
let split n set =
  let xp = (n, n) in
  let rec loop xp = function
    | Empty ->
      (Empty, false, Empty)
    | Node (l, v, r, _, _) ->
      let c = cmp xp v in
      if c = 0 then
        if fst v = n && snd v = n then (l, true, r) else
        if fst v = n then (l, true, add_one (fst v + 1, snd v) r) else
        if snd v = n then (add_one (fst v, snd v - 1) l, true, r) else
          (add_one (fst v, n - 1) l, true, add_one (n + 1, snd v) r)
      else if c < 0 then
        let (ll, pres, rl) = loop xp l in (ll, pres, join rl v r)
      else
        let (lr, pres, rr) = loop xp r in (join l v lr, pres, rr)
  in
  let setl, pres, setr = loop xp set in
  setl, pres, setr

(** removes interval [x] from the given set **)
let remove x = function
  | Node (l, k, r, _, _) as set ->
    let xl = fst x and xr = snd x in
    let pomxl, _, _ = split xl set in
    let _, _, pomxr = split xr set in
    (match (merge pomxl pomxr) with
     | Node (poml, pomk, pomr, _, _) -> join poml pomk pomr
     | Empty -> Empty)
  | Empty -> Empty

(** checks whether given and added intervals are separated **)
let checkl x k =
  if snd x + 1 = fst k then true else false

let checkr x k =
  if fst x - 1 = snd k then true else false

(** adds interval [x] to the given set, keeping all intervals separated **)
let rec add x = function
  | Node (l, k, r, h, _) as set ->
    let xl = fst x and xr = snd x in
    let pomxl, _, _ = split xl set in
    let _, _, pomxr = split xr set in
    (match pomxl, pomxr with
    | Node (_), Node (_) ->
      let maxl = max_elt pomxl in
      let minr = min_elt pomxr in
      let ppoml, ppomxl =
        if checkl maxl x then (remove_max_elt pomxl), fst maxl
        else
          pomxl, xl in
      let ppomr, ppomxr =
        if checkr minr x then (remove_min_elt pomxr), snd minr
        else
          pomxr, xr in
      join ppoml (ppomxl, ppomxr) ppomr
    | Empty, Node (_) ->
      let minr = min_elt pomxr in
      if checkr minr x then
        join Empty (fst x, snd minr) (remove_min_elt pomxr)
      else
        join Empty x pomxr
    | Node (_), Empty ->
      let maxl = max_elt pomxl in
      if checkl maxl x then
        join (remove_max_elt pomxl) (fst maxl, snd x) Empty
      else
        join pomxl x Empty
    | Empty, Empty ->  Node (Empty, x, Empty, 1, len x))
  | Empty -> Node (Empty, x, Empty, 1, len x)

(** checks whether value [n] is in the set [s] **)
let mem n s =
  let x= (n, n) in
  let rec loop = function
    | Node (l, k, r, _, _) ->
      let c = cmp x k in
      c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop s

(** applies [f] to all continous intervals of the set [s], in increasing order **)
let iter f s =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r in
  loop s

(** returns outcome of [f] applied to all continous intervals of the set [s] in increasing order **)
let fold f s acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
      loop (f k (loop acc l)) r in
  loop acc s

(** returns list of all intervals of set [s] in increasing order **)
let elements s =
  let rec loop acc = function
    | Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
  loop [] s

(** returns the number of elements not bigger than value [n] on the set [s] **)
let below n set =
  let pomxl, pres, _ = split n set in
  if pres then
    if num_el pomxl + 1 <= 0 then max_int else num_el pomxl + 1
  else
  if num_el pomxl < 0 then max_int else num_el pomxl

      (**                         Testy                              **)
(**    ////////////////////////////////////////////////////////////////     **)

(*
let zle = ref 0
let test (id:int) (result:bool) (expected:bool) : unit =
  if result <> expected then begin
    Printf.printf "Zly wynik testu %d!\n" id;
    incr zle
  end;;


let s = empty;;
test 11 (is_empty s) true;;
test 12 (is_empty (add (1, 1) s)) false;;

let s = add (10, 12) empty;;
test 21 (mem 9 s) false;;
test 22 (mem 10 s) true;;
test 23 (mem 12 s) true;;
test 24 (mem 13 s) false;;

let s = add (4, 7) s;;
test 25 (mem 8 s) false;;
test 26 (mem 11 s) true;;
test 27 (mem 5 s) true;;
test 28 (mem 3 s) false;;


let s = add (1, 1) (add (15, 16) (add (10, 14) (add (6, 9) empty)));;
test 31 (mem 10 (remove (10, 10) s)) false;;
test 32 (is_empty (remove (1, 20) s)) true;;
test 33 (mem 7 (remove (8, 15) s)) true;;

let s = add (-1, 1) (add (3, 7) (add (10, 12) (add (15, 18)
                                                 (add (-15, -13) empty))));;
let s = remove (-10, 12) s;;
test 34 (is_empty s) false;;
test 35 (mem 5 s) false;;
test 36 (mem (-10) s) false;;
test 37 (mem (-15) s) true;;
test 38 (mem 17 s) true;;


test 41 (elements (add (4, 5) (add (7, 8) empty)) = [(4, 5); (7, 8)]) true;;
test 42 (elements (add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty))))
         = [(1, 1); (4, 9); (11, 14)]) true;;


let s = add (3, 4) (add (8, 10) (add (15, 20) empty));;
test 51 (below 2 s = 0) true;;
test 52 (below 3 s = 1) true;;
test 53 (below 10 s = 5) true;;
test 54 (below 15 s = 6) true;;
test 55 (below 100 s = 11) true;;
let s = add (1, max_int) (add (-1, 0) empty);;
test 56 (below max_int s = max_int) true;;
let s = add (-min_int, max_int) empty;;
test 57 (below max_int s = max_int) true;;
test 58 (below min_int s = 1) true;;

let s = add (3, 4) (add (8, 10) (add (15, 20) empty));;
let l, pres, r = split 9 s;;
test 61 (mem 9 l) false;;
test 62 (mem 9 r) false;;
test 63 (mem 8 l) true;;
test 64 (mem 10 r) true;;
test 65 pres true;;
test 66 (mem 7 l) false;;
test 67 (mem 4 l) true;;
test 68 (mem 11 r) false;;
test 69 (mem 16 r) true;;


let s = add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty)));;
let a = ref [];;
let foo x = a := x::!a; ();;
test 71 (iter foo s; !a = [(11, 14); (4, 9); (1, 1)]) true;;


let s = add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty)));;
let foo x a = x::a;;
test 81 (fold foo s [] = [(11, 14); (4, 9); (1, 1)]) true;;


let _ =
  if !zle = 0 then
    ()
  else
    Printf.printf "\nZlych odpowiedzi: %d.\n" !zle
;;
*)
