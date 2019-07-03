fun paren s = "(" ^ s ^ ")"
fun pLn s = print (s ^ "\n")
structure Func =
struct
datatype t = C of real
   | X
   | Pair of t * t
   | Fst of t
   | Snd of t

fun layoutAux (C v, _) = Real.toString v
  | layoutAux (X, _) = "x"
  | layoutAux (Pair (f1, f2), ifp) =
    let
        val s = (layoutAux (f1, true)) ^ ", " ^ (layoutAux (f2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Fst f, ifp) =
    let
        val s = "#1·" ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Snd f, ifp) =
    let
        val s = "#2·" ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
and layout func = "λx." ^ layoutAux (func, true)

fun app (func, x) =
    case func of
        C v => C v
      | X => x
      | Pair (f1, f2) => Pair (app (f1, x), app (f2, x))
      | Fst f =>
        (case app (f, x) of
             Pair (y, _) => y
           | _ => raise Fail ("not a pair term: " ^ (layout (app (f, x))))
        )
      | Snd f =>
        (case app (f, x) of
             Pair (_, y) => y
           | _ => raise Fail ("not a pair term: " ^ (layout (app (f, x))))
        )
fun comp (f1, f2) =
    case f1 of
        C v => C v
      | X => f2
      | Pair (f11, f12) => Pair (comp (f11, f2), comp (f12, f2))
      | Fst f =>
        (case comp (f, f2) of
             Pair (y, _) => y
           | _ => raise Fail ("not a pair term: " ^ (layout (app (f, f2))))
        )
      | Snd f =>
        (case comp (f, f2) of
             Pair (_, y) => y
           | _ => raise Fail ("not a pair term: " ^ (layout (app (f, f2))))
        )
fun duplicate n =
    if n < 1 then raise Fail "bad id"
    else if n = 1 then X
    else Pair (X, duplicate (n - 1))
end

(* structure Linear = *)
(* struct *)
(* type t = real *)

(* fun layout lin = Real.toString lin *)
(* end *)

signature CAT =
sig
    type object
    type arrow
    val id: object -> arrow
    val dom: arrow -> object
    val codom : arrow -> object
    val circ : arrow -> arrow -> arrow
end

structure Mlfunc =
struct
structure F = Func
type dimension = int
type object = dimension
type arrow = {dom : object, codom : object, func: F.t}
fun id dim = {dom = dim, codom = dim, func = F.X}
fun dom {dom, codom, func} = dom
fun codom {dom, codom, func} = codom
fun circ {dom = dom1, codom = codom1, func = func1}
         {dom = dom2, codom = codom2, func = func2} =
    let
        val _ = if codom2 = dom1 then () else print "domain does not match, can't compose!\n"
    in
        {dom = dom2, codom = codom1, func = F.comp (func1, func2)}
    end
fun layout {dom, codom, func} =
    let
        val ty = (Int.toString dom) ^ " ⇒ " ^ (Int.toString codom)
    in
        (F.layout func) ^ ": " ^ ty
    end
end


(* structure D = *)
(* struct *)
(* structure M = Mlfunc *)
(* type object = M.dimension *)
(* type linear = real -> real *)
(* type arrow = {dom : object, codom : object, func: real -> real * linear} *)
(* fun id dim = *)
(*     {dom = dim, codom = dim, func = fn x => (x, fn x => x)} *)
(* fun dom {dom, codom, func} = dom *)
(* fun codom {dom, codom, func} = codom *)
(* fun circ {dom1, codom1, func1} {dom2, codom2, func2} = *)
(*     let *)
(*         val _ = if codom2 = dom1 then () else print "domain does not match, can't compose1\n" *)
(*         fun func x = *)
(*             let *)
(*                 val (y, linear2) = func2 x *)
(*                 val (z, linear1) = func1 y *)
(*             in *)
(*                 (z, fn x => linear2 (linear1 x)) *)
(*             end *)
(*     in *)
(*         {dom = dom2, codom = codom1, func = func} *)
(*     end *)
(* end; *)

(* structure DPlus = *)
(* struct *)
(* structure M = Mlfunc *)
(* structure D = D *)
(* fun dplus {dom, codom, func} = *)
(*     let *)
(*     in *)
(*     end *)
(* end *)
open Func;
structure M = Mlfunc;
let
    val arr1 = M.id 3
    val arr2 = M.id 2
    val _ = pLn (M.layout arr1)
    val _ = pLn (M.layout (M.circ arr1 arr1))
    val _ = pLn (M.layout (M.circ arr1 arr2))
in
    ()
end;
