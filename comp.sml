fun paren s = "(" ^ s ^ ")"
fun pLn s = print (s ^ "\n")
structure Func =
struct
datatype t = Value of real
           | Var
           | Sum of t * t
           | Product of t * t
           | Neg of t
           | Comp of t * t
fun toF func =
    case func of
        Value v => (fn _ => v)
      | Var => (fn x => x)
      | Sum (func1, func2) =>
        (fn x => ((toF func1) x) + ((toF func2) x))
      | Product (func1, func2) =>
        (fn x => ((toF func1) x) * ((toF func2) x))
      | Neg f => (fn x => ~ ((toF f) x))
      | Comp (f1, f2) =>
        (fn x => (toF f1) ((toF f2) x))

fun layoutAux (Value v, _) = Real.toString v
  | layoutAux (Var, _) = "x"
  | layoutAux (Sum (f1, f2), ifp) =
    let
        val s = (layoutAux (f1, true)) ^ " + " ^ (layoutAux (f2, true))
    in
        if ifp then paren s else s
    end
  | layoutAux (Product (f1, f2), ifp) =
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
  | layoutAux (Comp (f1, f2), ifp) =
    let
        val s = (layout f1) ^ " ∘ " ^ (layout f2)
    in
        if ifp then paren s else s
    end
and layout func = "λx." ^ layoutAux (func, true)
end

structure Ad =
struct
open Func
type ad = real
type a = real
type b = real
type c = real
type d = t * (a -> ad)

fun adAux f x =
    case f of
        Value _ => Value 0.0
      | Var => Var
      | Sum (f1, f2) => Sum (adAux f1 x, adAux f2 x)
      | Product (f1, f2) =>
        let
            val b1 = (toF f1) x
            val b2 = (toF f2) x
            val ad1 = adAux f1 x
            val ad2 = adAux f2 x
        in
            Sum (Product (Value b1, ad2),
                 Product (Value b2, ad1))
        end
      | Neg f => Neg (adAux f x)
      | Comp (f1, f2) =>
        let
            val (b, d2) = ad f2 x
            val (_, d1) = ad f1 b
        in
            Comp (d1, d2)
        end
and ad f x =
    let
        val b = (toF f) x
        val d = adAux f x
    in
        (b, d)
    end
end

open Func;
open Ad;
let
    fun pResult (result, diff) = pLn ("result: " ^ (Real.toString result) ^ ", f': " ^ (layout diff) ^ ", diff: " ^ (Real.toString ((toF diff) 1.0)))
    val f1 = Sum (Product (Value 3.0, Var), Value 2.0)
    val _ = pLn (layout f1)
    val _ = pResult (ad f1 4.0)
    val f2 = (Sum (Product (Value ~4.5, Var), Value 7.8))
    val _ = pLn (layout f2)
    val _ = pResult (ad f2 4.0)
    val f3 = Comp (f1, f2)
    val _ = pLn (layout f3)
    val _ = pResult (ad f3 4.0)
    val f4 = Product (f1, f2)
    val _ = pLn (layout f4)
    val _ = pResult (ad f4 4.0)
in
    ()
end;
