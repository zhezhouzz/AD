fun paren s = "(" ^ s ^ ")"
fun pLn s = print (s ^ "\n")
fun list2string (f, l) =
    let
        val r = List.foldl (fn (e, r) =>
                               case r of
                                   NONE => SOME (f e)
                                 | SOME s => SOME (s ^ ", " ^ (f e))
                           ) NONE l
    in
        case r of
            NONE => "[]"
          | SOME r => "[" ^ r ^ "]"
    end


structure Func =
struct
datatype t = C of real
           | X
           | Tuple of t list
           | Nth of t * int
           | Mul of t * t
           | Add of t * t
           | Map of t * t
           | Fadd of t
           | Neg of t
           | None
fun layoutAux (C v, _) = Real.toString v
  | layoutAux (X, _) = "x"
  | layoutAux (Tuple l, ifp) =
    let
        val s = list2string (fn e => layoutAux (e, false), l)
    in
        s
    end
  | layoutAux (Nth (f, i), ifp) =
    let
        val s = "#" ^ (Int.toString i) ^ "·" ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Add (f1, f2), ifp) =
    let
        val s = (layoutAux (f1, true)) ^ " + " ^ (layoutAux (f2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Mul (f1, f2), ifp) =
    let
        val s = (layoutAux (f1, true)) ^ " × " ^ (layoutAux (f2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Fadd f, ifp) =
    let
        val s = "⊕ " ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Map (f, l), ifp) =
    let
        val s = (layoutAux (l, true)) ^ " ⊗ " ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Neg f, ifp) =
    let
        val s = "~ " ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (None, _) = "0"
and layout func = "λx." ^ layoutAux (func, true)

fun comp (f1, f2) =
    case f1 of
        C v => C v
      | X => f2
      | Tuple l => Tuple (List.map (fn e => comp (e, f2)) l)
      | Nth (f1, i) => Nth (comp (f1, f2), i)
      | Add (f11, f12) => Add (comp (f11, f2), comp (f12, f2))
      | Mul (f11, f12) => Mul (comp (f11, f2), comp (f12, f2))
      | Fadd f1 => Fadd (comp (f1, f2))
      | Map (f1, l) => Map (f1, comp (l, f2))
      | Neg f => Neg (comp (f, f2))
      | None => None
fun eval func =
    case func of
        C v => C v
      | X => X
      | Tuple l => Tuple (List.map eval l)
      | Nth (f1, i) =>
        (case eval f1 of
             Tuple l => List.nth (l, i)
           | f1 => Nth (f1, i)
        )
      | Add (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 + v2)
           | (None, f2) => f2
           | (f1, None) => f1
           | (Tuple f1, Tuple f2) =>
             Tuple (ListPair.map (fn (e1, e2) => eval (Add (e1, e2))) (f1, f2))
           | (f1, f2) => Add (f1, f2)
        )
      | Mul (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 * v2)
           | (None, f2) => None
           | (f1, None) => None
           | (Tuple f1, Tuple f2) =>
             Tuple (ListPair.map (fn (e1, e2) => eval (Mul (e1, e2))) (f1, f2))
           | (f1, f2) => Mul (f1, f2)
        )
      | Fadd f =>
        (case eval f of
             Tuple f =>
             let
                 val r = List.foldl (fn (e, r) =>
                                        case r of
                                            NONE => SOME e
                                          | SOME r => SOME (Add (r, e))
                                    ) NONE f
             in
                 case r of
                     NONE => None
                   | SOME r => eval r
             end
           | f => Fadd f
        )
      | Map (f, l) =>
        (case eval l of
             Tuple l =>
             let
                 val r = List.map (fn e => comp (f, e)) l
             in
                 eval (Tuple r)
             end
          | f => Map f
        )
      | Neg f =>
        (case eval f of
             C v => C (~v)
           | None => None
           | Tuple f => Tuple (List.map eval f)
           | f => Neg f
        )
      | None => None
(* fun vec (n, v) = *)
(*     if n < 1 then raise Fail "bad vec" *)
(*     else if n = 1 then v *)
(*     else Pair (v, vec (n - 1, v)) *)
fun hop (n, i, v) =
    let
        val none = List.tabulate (n, fn j => if i = j then v else None)
    in
        Tuple none
    end
end


structure DPlus =
struct
open Func
fun ad (func, x) =
    case func of
        C v => None
      | X => X
      | Tuple l => Tuple (List.map (fn e => ad (e, x)) l)
      | Nth (f, i) => Nth (ad (f, x), i)
      | Add (f1, f2) => Add (ad (f1, x), ad (f2, x))
      | Mul (f1, f2) =>
        let
            val d1 = ad (f1, x)
            val v1 = eval (comp (f1, x))
            val d2 = ad (f2, x)
            val v2 = eval (comp (f2, x))
        in
            Add (Mul (v2, d1), Mul (v1, d2))
        end
      | Neg f => Neg (ad (f, x))
      | Fadd f => Fadd (ad (f, x))
      | Map (f, l) => Map (ad (f, x), ad (l, x))
      | None => None
fun toDiffAux (dom, i, func) =
    let
        val hop = hop (dom, i, X)
        val diff = comp (func X, hop)
        val y0 = comp (diff, None)
        val y1 = comp (diff, C 1.0)
        val diff = Add (y1, Neg y0)
    in
        eval diff
    end
fun toDiff {dom, codom, funcd = (_, func)} =
    let
        val result = List.tabulate (dom, fn i => i)
        val result = List.map (fn i => toDiffAux (dom, i, func)) result
    in
        result
    end
end;

structure D =
struct
structure F = Func
type dimension = int
type object = dimension
type arrow = {dom : object, codom : object, funcd: F.t * (F.t -> F.t)}
fun id dim = {dom = dim, codom = dim, funcd = (F.X, fn x => F.X)}
fun dom {dom, codom, funcd} = dom
fun codom {dom, codom, funcd} = codom
fun circ {dom = dom1, codom = codom1, funcd = (f1, fd1)}
         {dom = dom2, codom = codom2, funcd = (f2, fd2)} =
    let
        val _ = if codom2 = dom1 then () else print "domain does not match, can't compose1\n"
        val f = F.comp (f1, f2)
        fun d x =
            let
                val y = F.comp (f2, x)
                val linear2 = fd2 x
                val linear1 = fd1 y
            in
                F.comp (linear1, linear2)
            end
    in
        {dom = dom2, codom = codom1, funcd = (f, d)}
    end
fun layout {dom, codom, funcd = (f, d)} =
    let
        val ty = (Int.toString dom) ^ " ⇒ " ^ (Int.toString codom)
    in
        (F.layout (F.eval f)) ^ " ≈ " ^ (F.layout (F.eval (d F.X))) ^ ": " ^ ty
    end
fun new (dom, codom, func) =
    {dom = dom, codom = codom, funcd = (func, fn x => DPlus.ad (func, x))}
fun value (dom, func) =
    {dom = dom, codom = dom, funcd = (func, fn x => F.X)}
end;

open Func;
let
    val arr1 = D.new (4, 1, Fadd (Mul (X, X)))
    val v1 = D.value (4, Tuple [C 1.0, C 2.0, C 3.0, C 4.0])
    val r1 = D.circ arr1 v1
    val _ = pLn (D.layout arr1)
    val _ = pLn (D.layout r1)
    val _ = pLn (list2string (fn e => layoutAux (e, true), DPlus.toDiff r1))
in
    ()
end;
