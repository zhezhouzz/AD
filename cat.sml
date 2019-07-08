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
           | Pair of t * t
           | Fst of t
           | Snd of t
           | Add of t * t
           | Mul of t * t
           | Neg of t
           | Sin of t
           | Cos of t
           | Exp of t
           | None

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
  | layoutAux (Neg f, ifp) =
    let
        val s = "~ " ^ (layoutAux (f, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (None, _) = "nan"
  | layoutAux (Sin f, _) = "sin(" ^ (layoutAux (f, false))  ^ ")"
  | layoutAux (Cos f, _) = "cos(" ^ (layoutAux (f, false))  ^ ")"
  | layoutAux (Exp f, _) = "e^(" ^ (layoutAux (f, false))  ^ ")"
and layout func = "λx." ^ layoutAux (func, true)

fun app (func, x) =
    case func of
        C v => C v
      | X => x
      | Pair (f1, f2) => Pair (app (f1, x), app (f2, x))
      | Fst f => Fst (app (f, x))
      | Snd f => Snd (app (f, x))
      | Add (f1, f2) => Add (app (f1, x), app (f2, x))
      | Mul (f1, f2) => Mul (app (f1, x), app (f2, x))
      | Neg f => Neg (app (f, x))
      | None => None
      | Sin f => Sin (app (f, x))
      | Cos f => Cos (app (f, x))
      | Exp f => Exp (app (f, x))
fun comp (f1, f2) =
    case f1 of
        C v => C v
      | X => f2
      | Pair (f11, f12) => Pair (comp (f11, f2), comp (f12, f2))
      | Fst f => Fst (comp (f, f2))
      | Snd f => Snd (comp (f, f2))
      | Add (f11, f12) => Add (comp (f11, f2), comp (f12, f2))
      | Mul (f11, f12) => Mul (comp (f11, f2), comp (f12, f2))
      | Neg f => Neg (comp (f, f2))
      | None => None
      | Sin f => Sin (comp (f, f2))
      | Cos f => Cos (comp (f, f2))
      | Exp f => Exp (comp (f, f2))
fun duplicate n =
    if n < 1 then raise Fail "bad id"
    else if n = 1 then X
    else Pair (X, duplicate (n - 1))
fun eval func =
    case func of
        C v => C v
      | X => X
      | Pair (f1, f2) => Pair (eval f1, eval f2)
      | Fst f =>
        (case eval f of
             Pair (y, _) => y
           | None => None
           | f => Fst f
        )
      | Snd f =>
        (case eval f of
             Pair (_, y) => y
           | None => None
           | _ => Snd f
        )
      | Add (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 + v2)
           | (None, f2) => f2
           | (f1, None) => f1
           | (Pair (v11, v12), Pair (v21, v22)) =>
             Pair (eval (Add (v11, v21)), eval (Add (v12, v22)))
           | (f1, f2) => Add (f1, f2)
        )
      | Mul (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 * v2)
           | (None, _) => None
           | (_, None) => None
           | (Pair (v11, v12), Pair (v21, v22)) =>
             Pair (eval (Mul (v11, v21)), eval (Mul (v12, v22)))
           | (f1, f2) => Mul (f1, f2)
        )
      | Neg f =>
        (case eval f of
             C v => C (~v)
           | None => None
           | Pair (f1, f2) => Pair (eval (Neg f1), eval (Neg f2))
           | f => Neg f
        )
      | Sin f =>
        (case eval f of
             None => None
           | C v => C (Math.sin v)
           | Pair (f1, f2) => Pair (eval (Sin f1), eval (Sin f2))
           | f => Sin f
        )
      | Cos f =>
        (case eval f of
             None => None
           | C v => C (Math.cos v)
           | Pair (f1, f2) => Pair (eval (Cos f1), eval (Cos f2))
           | f => Cos f
        )
      | Exp f =>
        (case eval f of
             None => None
           | C v => C (Math.exp v)
           | Pair (f1, f2) => Pair (eval (Exp f1), eval (Exp f2))
           | f => Exp f
        )
      | None => None
fun vec (n, v) =
    if n < 1 then raise Fail "bad vec"
    else if n = 1 then v
    else Pair (v, vec (n - 1, v))
fun hopAux (n, i, v) =
    if n = i then v else None
fun hop (n, i, v) =
    if n < 1 then raise Fail "bad vec"
    else if n = 1 then hopAux (n, i, v)
    else Pair (hopAux (n, i, v), hop (n - 1, i, v))
end

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

structure Linear =
struct
structure F = Func
type t = real
fun toFunc t = F.Mul (F.C t, F.X)
end


structure D =
struct
structure F = Func
structure M = Mlfunc
type object = M.dimension
type arrow = {dom : object, codom : object, funcd: F.t * F.t}
fun id dim = {dom = dim, codom = dim, funcd = (F.X, F.X)}
fun dom {dom, codom, funcd} = dom
fun codom {dom, codom, funcd} = codom
fun circ {dom = dom1, codom = codom1, funcd = (funcd11, funcd12)}
         {dom = dom2, codom = codom2, funcd = (funcd21, funcd22)} =
    let
        val _ = if codom2 = dom1 then () else print "domain does not match, can't compose1\n"
        fun funcd x =
            let
                val y = F.app (funcd21, x)
                val linear2 = F.app (funcd22, x)
                val z = F.app (funcd11, y)
                val linear1 = F.app (funcd12, y)
            in
                (z, fn x => F.comp (linear1, linear2))
            end
    in
        {dom = dom2, codom = codom1, funcd = funcd}
    end
fun layout {dom, codom, funcd = (funcd1, funcd2)} =
    let
        val ty = (Int.toString dom) ^ " ⇒ " ^ (Int.toString codom)
    in
        (F.layout (F.eval funcd1)) ^ " ≈ " ^ (F.layout (F.eval funcd2)) ^ ": " ^ ty
    end
end;

structure DPlus =
struct
structure M = Mlfunc
structure D = D
open Func
fun ad (func, x) =
    case func of
        C v => None
      | X => X
      | Pair (f1, f2) => Pair (ad (f1, x), ad (f2, x))
      | Fst f => Fst (ad (f, x))
      | Snd f => Snd (ad (f, x))
      | Add (f1, f2) => Add (ad (f1, x), ad (f2, x))
      | Mul (f1, f2) =>
        let
            val d1 = ad (f1, x)
            val v1 = eval (app (f1, x))
            val d2 = ad (f2, x)
            val v2 = eval (app (f2, x))
        in
            Add (Mul (d1, v2), Mul (d2, v1))
        end
      | Neg f => Neg (ad (f, x))
      | None => None
      | Sin f =>
        let
            val d = ad (f, x)
            val v = eval (app (Cos f, x))
        in
            Mul (v, d)
        end
      | Cos f =>
        let
            val d = ad (f, x)
            val v = eval (Neg (app (Sin f, x)))
        in
            Mul (v, d)
        end
      | Exp f =>
        let
            val d = ad (f, x)
            val v = eval (app (Exp f, x))
        in
            Mul (v, d)
        end
fun dplus ({dom, codom, func}, x) = {dom = dom, codom = codom, funcd = (func, ad ((eval func), x))}
fun toDiffAux (dom, i, func) =
    let
        val x0 = vec (dom, C 0.0)
        val x1 = hop (dom, i, C 1.0)
        (* val _ = print ((layout x1) ^ "\n") *)
        val y0 = eval (app (func, x0))
        val y1 = eval (app (func, x1))
    in
        eval (Add (y1, Neg y0))
    end
fun toDiff {dom, codom, funcd = (_, func)} =
    let
        val result = List.tabulate (dom, fn i => i + 1)
        val result = List.map (fn i => toDiffAux (dom, i, func)) result
    in
        result
    end
end

open Func;
structure M = Mlfunc;
let
    val arr1 = M.id 3
    val arr2 = M.id 2
    val _ = pLn (M.layout arr1)
    val _ = pLn (M.layout (M.circ arr1 arr1))
    val _ = pLn (M.layout (M.circ arr1 arr2))
    val ad1 = D.id 3
    val _ = pLn (D.layout ad1)
    val ad2 = DPlus.dplus (arr1, C 0.0)
    val _ = pLn (D.layout ad1)
    val arr3 = {dom = 1, codom = 1, func = Add (Mul (C 3.0, X), C 4.0)}
    val arr4 = {dom = 1, codom = 1, func = Add (Mul (C 3.0, X), C 4.0)}
    val arr5 = M.circ arr3 arr4
    val _ = pLn (D.layout (DPlus.dplus (arr3, C 0.0)))
    val _ = pLn (D.layout (DPlus.dplus (arr5, C 0.0)))
    val arr6 = {dom = 1, codom = 2, func = Pair (Add (Mul (C 3.0, X), C 4.0), Add (Mul (C 4.0, X), C 1.0))}
    val arr7 = {dom = 2, codom = 1, func = Mul (Mul (C 2.0, Fst X), Snd X)}
    val arr8 = M.circ arr7 arr6
    val _ = pLn ("f₁:\n" ^ (M.layout arr6))
    val _ = pLn ("f₂:\n" ^ (M.layout arr7))
    val _ = pLn ("f₁ ∘ f₂ :\n" ^ (M.layout arr8))
    val d8 = DPlus.dplus (arr8, C 0.0)
    val v1 = C 0.0
    val _ = pLn ("Diff f₁ ∘ f₂ in " ^ (layout v1) ^ " :\n" ^ (D.layout d8))
    val _ = pLn (list2string (layout, DPlus.toDiff (DPlus.dplus (arr8, v1))))
    val v2 =  Pair (C 2.0, C 3.0)
    val arr9 = M.circ arr6 arr7
    val _ = pLn ("f₂ ∘ f₁ :\n" ^ (M.layout arr9))
    val d9 = DPlus.dplus (arr9, v2)
    val _ = pLn ("Diff f₂ ∘ f₁ in " ^ (layout v2) ^ " :\n" ^ (D.layout d9))
    val _ = pLn (list2string (layout, DPlus.toDiff d9))
    val arr10 = {dom = 1, codom = 2, func = Pair (Sin (Mul (C 3.0, X)), Cos (Add (Mul (C 4.0, X), C 1.0)))}
    val v3 = C 1.0
    val d10 = DPlus.dplus (arr10, v3)
    val _ = pLn ("Diff f₁₀ in " ^ (layout v3) ^ " :\n" ^ (D.layout d10))
    val _ = pLn (list2string (layout, DPlus.toDiff d10))
    val arr11 = M.circ arr7 (M.circ arr10 (M.circ arr7 arr10))
    (* val arr11 = M.circ arr10 (M.circ arr7 arr10) *)
    (* val arr11 = M.circ arr10 arr7 *)
    val v4 = Pair (C 1.0, C 1.0)
    val d11 = DPlus.dplus (arr11, v3)
    val _ = pLn ("Diff f₁₁ in " ^ (layout v3) ^ " :\n" ^ (D.layout d11))
    val _ = pLn (list2string (layout, DPlus.toDiff d11))
in
    ()
end;
