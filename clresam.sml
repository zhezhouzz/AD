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

datatype t = C of real
           | Var of string
           | Id
           | Limit of int * string * t
           | Fadd
           | Add
           | Mul
           | Pair of t * t
           | Left
           | Right
           | Circ of t * t

fun add2 (a, b) = Circ (Add, Pair (a, b))
fun mul2 (a, b) = Circ (Mul, Pair (a, b))
fun left e = Circ (Left, e)
fun right e = Circ (Right, e)

fun layoutFunc (C v, _) = Real.toString v
  | layoutFunc (Var x, _) = x
  | layoutFunc (Id, _) = "id"
  | layoutFunc (Limit (i, x, body), _) = "tab[" ^ x ^ " in " ^ (Int.toString i) ^ ": " ^ (layoutFunc (body, false)) ^ "]"
  | layoutFunc (Fadd, _) = "⊕"
    (* let *)
    (*     val s = "⊕ " ^ (layoutFunc (vec, true)) *)
    (* in *)
    (*     if ifp then paren s else s *)
    (* end *)
  | layoutFunc (Add, _) = "addC"
  | layoutFunc (Mul, _) = "mulC"
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

fun layout func = layoutFunc (func, true)

fun subst (body, id, e) =
    let
        fun aux body =
            case body of
                (C v) => C v
              | Var y => if id = y then e else Var y
              | Id => Id
              | Limit (len, y, body) =>
                if id = y then Limit (len, y, body) else Limit (len, y, aux body)
              | Fadd => Fadd
              | Add => Add
              | Mul => Mul
              | Pair (b1, b2) => Pair (subst (b1, id, e), subst (b2, id, e))
              | Left => Left
              | Right => Right
              | Circ (b1, b2) => Circ (subst (b1, id, e), subst (b2, id, e))
    in
        aux body
    end

fun eval (f, v: t) : t =
    let
        fun evalAdd (C a, C b) = C (a + b)
          | evalAdd (Limit (len1, x1, f1), Limit (len2, x2, f2)) =
            let
                val x = newSym ()
                val f1 = subst (f1, x1, Id)
                val f2 = subst (f2, x2, Id)
                val f = add2 (f1, f2)
            in
                Limit (len1, x, f)
            end
          | evalAdd (Pair (v11, v12), Pair (v21, v22)) = Pair (evalAdd (v11, v12), evalAdd (v21, v22))
          | evalAdd (a, b) = add2 (a, b)
        fun evalMul (C a, C b) = C (a * b)
          | evalMul (Limit (len1, x1, f1), Limit (len2, x2, f2)) =
            let
                val x = newSym ()
                (* val _ = pLn (layout f1) *)
                val f1 = subst (f1, x1, Id)
                (* val _ = pLn (layout f1) *)
                val f2 = subst (f2, x2, Id)
                val f = mul2 (f1, f2)
            in
                Limit (len1, x, f)
            end
          | evalMul (Pair (v11, v12), Pair (v21, v22)) = Pair (evalMul (v11, v12), evalMul (v21, v22))
          | evalMul (a, b) = mul2 (a, b)
    in
        case (f, v) of
            (C v, _) => C v
          | (Id, v) => v
          | (Var x, _) => Var x
          | (Limit (len, x, body), v) => Limit (len, x, eval (body, v))
          | (Fadd, Limit (len, x, body)) =>
            let
                val body = subst (body, x, Id)
                val base = List.tabulate (len, fn i => C (Real.fromInt i))
                val res = List.map (fn v => eval (body, v)) base
                val r = List.foldl (fn (e, r) =>
                                       case r of
                                           NONE => SOME e
                                         | SOME r => SOME (add2 (r, e))
                                   ) NONE res
            in
                case r of
                    NONE => raise Fail "eval: Fadd"
                  | SOME r => eval (r, v)
            end
          | (Add, Pair (a, b)) => evalAdd (a, b)
          | (Mul, Pair (a, b)) => evalMul (a, b)
          | (Pair (f1, f2), v) => Pair (eval (f1, v), eval (f2, v))
          | (Left, Pair (a, b)) => a
          | (Right, Pair (a, b)) => b
          | (Circ (f1, f2), v) => eval (f1, eval (f2, v))
          | _ => raise Fail ("eval: " ^ (layout f) ^ " in " ^  (layout v))
    end
fun pLnEval (f, v) =
    let
        val r = eval (f, v)
        val s = (layout f) ^ ": " ^ (layout v) ^ " -> " ^ (layout r)
    in
        pLn s
    end
fun pLnVec (Limit (len, x, body)) =
    let
        val body = subst (body, x, Id)
        val base = List.tabulate (len, fn i => C (Real.fromInt i))
        val res = List.map (fn v => eval (body, v)) base
        val s = list2string (layout, res)
    in
        pLn s
    end
  | pLnVec _ = raise Fail "pLnVec: not a vec"
end

open Func;
let
    val fun1 = add2 (C 1.0, mul2 (C 2.0, Id))
    val _ = pLnEval (fun1, C 0.0)
    val _ = pLnEval (fun1, C 1.0)
    val _ = pLnEval (fun1, C 2.0)
    (* val _ = pLnDiff (fun1, C 0.0) *)
    (* val _ = pLnDiff (fun1, C 1.0) *)
    (* val _ = pLnDiff (fun1, C 2.0) *)
    val vec1 = Limit (6, "x", add2 (C 1.0, mul2 (C 2.0, Var "x")))
    val _ = pLn (layout vec1)
    val _ = pLnVec vec1
    val elemwise = mul2 (Id, Id)
    val _ = pLn (layout elemwise)
    val fun2 = Circ (elemwise, fun1)
    val _ = pLnEval (fun2, C 0.0)
    val _ = pLnEval (fun2, C 1.0)
    val _ = pLnEval (fun2, C 2.0)
    val _ = pLnEval (elemwise, vec1)
    val _ = pLnVec (eval (elemwise, vec1))
    val dot = Circ (Fadd, mul2 (Id, Id))
    val _ = pLn (layout dot)
    val _ = pLnEval (dot, vec1)
    (* val _ = pLnDiff (fun2, R 0.0) *)
    (* val _ = pLnDiff (fun2, R 1.0) *)
    (* val _ = pLnDiff (fun2, R 2.0) *)
in
    ()
end;
