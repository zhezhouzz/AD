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
val counter = ref 0
fun newSym () =
    let
        val ret = "k" ^ (Int.toString (!counter))
        val _ = counter := ((!counter) + 1)
    in
        ret
    end


structure Func =
struct
datatype t = C of v
           | Id
           | Add
           | Mul
           | Fadd of int
           | Pair of t * t
           | Left
           | Right
           | Circ of t * t
     and v = R of real
           | VPair of v * v
           | Vec of int * t
           | None

datatype d = scale of Real
           | dup of d * d
           | jam of d * d

fun circs l =
    let
        val r = List.foldr (fn (e, r) =>
                               case r of
                                   NONE => SOME e
                                 | SOME r => SOME (Circ (e, r))
                           ) NONE l
    in
        case r of
            NONE => Id
          | SOME r => r
    end
fun add2 (a, b) = Circ (Add, Pair (a, b))
fun mul2 (a, b) = Circ (Mul, Pair (a, b))
fun left e = Circ (Left, e)
fun right e = Circ (Right, e)

fun layoutFunc (C v, _) = layoutValue v
  | layoutFunc (Id, _) = "id"
  | layoutFunc (Add, _) = "addC"
  | layoutFunc (Mul, _) = "mulC"
  | layoutFunc (Fadd len, _) = "faddC[" ^ (Int.toString len) ^"]"
  | layoutFunc (Pair (e1, e2), ifp) =
    let
        val s = (layoutFunc (e1, true)) ^ " △ " ^ (layoutFunc (e2, true))
    in
        if ifp then paren s else s
    end
  | layoutFunc (Left, ifp) = "exl"
  | layoutFunc (Right, ifp) = "exr"
  | layoutFunc (Circ (e1, e2), ifp) =
    let
        val s = (layoutFunc (e1, true)) ^ " ∘ " ^ (layoutFunc (e2, true))
    in
        if ifp then paren s else s
    end
and layoutValue (R r) = Real.toString r
  | layoutValue (VPair (a, b)) = paren ((layoutValue a) ^ ", " ^ (layoutValue b))
  | layoutValue (Vec (len, f)) = "[" ^ (Int.toString len) ^ ": " ^ (layoutFunc (f, false)) ^ "]"
  | layoutValue (None) = "0"

fun layout func = layoutFunc (func, true)

fun slope func =
    let
        val 
    in
    end

fun eval (f, v) =
    case (f, v) of
        (_, None) => None
      | (C v, _) => v
      | (Id, v) => v
      | (Add, VPair (a, b)) =>
        (case (a, b) of
             (R a, R b) => R (a + b)
           | (None, R b) => R b
           | (R a, None) => R a
           | (Vec (len1, func1), Vec (len2, func2)) =>
             
           | _ => raise Fail "eval: Add"
        )
      | (Fadd len, vec) =>
        (case vec of
             Vec (len, func) =>
             let
                 val base = List.tabulate (len, fn i => R (Real.fromInt i))
                                          val r = 
                 eval (func, )
             in
             end
           | _ => raise Fail "eval: Add"
        )
      | (Mul, VPair (a, b)) =>
        (case (a, b) of
             (R a, R b) => R (a * b)
           | (None, _) => None
           | (_, None) => None
           | _ => raise Fail ("eval: Mul " ^ (layoutValue (VPair (a, b))))
        )
      | (Pair (f1, f2), v) => VPair (eval (f1, v), eval (f2, v))
      | (Left, VPair (a, b)) => a
      | (Right, VPair (a, b)) => b
      | (Circ (f1, f2), v) => eval (f1, eval (f2, v))
      | _ => raise Fail ("eval: " ^ (layout f) ^ " in " ^  (layoutValue v))
fun pe func =
    case func of
        C v =>
        (case v of
             VPair (a, b) => Pair (pe (C a), pe (C b))
           | x => C x
        )
      | Circ (f1, f2) =>
        (case (pe f1, pe f2) of
             (a, Id) => a
           | (Id, b) => b
           | (Add, (Pair (C None, b))) => b
           | (Add, (Pair (a, C None))) => a
           | (Mul, (Pair (C None, _))) => C None
           | (Mul, (Pair (_, C None))) => C None
           | (Pair (f1, f2), b) => Pair (pe (Circ (f1, b)), pe (Circ (f2, b)))
           | (Left, Pair (a, b)) => a
           | (Right, Pair (a, b)) => b
           | (C v, _) => C v
           | (Circ (f, g), k) => pe (Circ (f, Circ (g, k)))
           | (f1, f2) => Circ (f1, f2)
        )
      | Pair (a, b) => Pair (pe a, pe b)
      | x => x
fun ad func : (v -> t)=
    case func of
        C v => (fn v => C None)
      | Id =>
        (fn (v: v) => Id)
      | Add =>
        (fn v => Add)
      | Mul =>
        (fn v =>
            add2 (mul2 (left (C v), right Id), mul2 (right (C v), left Id))
        )
      | Pair (f1, f2) =>
        (fn v =>
            Pair ((ad f1) v, (ad f2) v)
        )
      | Left =>
        (fn v => Left)
      | Right =>
        (fn v => Right)
      | Circ (f1, f2) =>
        (fn v =>
            let
                val v2 = eval (f2, v)
                val d2 = (ad f2) v
                val d1 = (ad f1) v2
            in
                Circ (d1, d2)
            end
        )
fun pLnEval (f, v) =
    let
        val r = eval (f, v)
        val s = (layout (pe f)) ^ ": " ^ (layoutValue v) ^ " -> " ^ (layoutValue r)
    in
        s
    end
fun pLnDiff (f, v) = pLnEval (f v, v)
end

open Func;
let
    val fun1 = add2 (C (R 1.0), mul2 (C (R 2.0), Id))
    val _ = pLn (pLnEval (fun1, R 0.0))
    val _ = pLn (pLnEval (fun1, R 1.0))
    val _ = pLn (pLnEval (fun1, R 2.0))
    val d1 = ad fun1
    val _ = pLn (pLnDiff (d1, R 0.0))
    val _ = pLn (pLnDiff (d1, R 1.0))
    val _ = pLn (pLnDiff (d1, R 2.0))
    val vec1 =  Vec (6, fun1)
    val _ = pLn (layoutValue vec1)
    val elemwise = mul2(Id, Id)
    val _ = pLn (layout elemwise)
    val fun2 = Circ (elemwise, fun1)
    val _ = pLn (pLnEval (fun2, R 0.0))
    val _ = pLn (pLnEval (fun2, R 1.0))
    val _ = pLn (pLnEval (fun2, R 2.0))
    val d2 = (ad fun2) (R 0.0)
    val _ = pLn (pLnEval (d2, R 0.0))
    val _ = pLn (pLnEval (d2, R 1.0))
    val _ = pLn (pLnEval (d2, R 2.0))
    val d2 = (ad fun2) (R 1.0)
    val _ = pLn (pLnEval (d2, R 0.0))
    val _ = pLn (pLnEval (d2, R 1.0))
    val _ = pLn (pLnEval (d2, R 2.0))
in
    ()
end;
