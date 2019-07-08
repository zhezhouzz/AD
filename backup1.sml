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
           | V of string
           | Vector of t list
           | Nth of t * int
           | Mul of t * t
           | Add of t * t
           | Map of t * t
           | Fadd of t
           | Neg of t
           | Lam of string * t
           | Ap of t * t
           | Piece of t * int
           | None
fun layoutAux (C v, _) = Real.toString v
  | layoutAux (V x, _) = x
  | layoutAux (Vector l, ifp) =
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
  | layoutAux (Lam (x, body), _) =
    let
        val s = layoutAux (body, true)
    in
        "λ" ^ x ^ "." ^ s
    end
  | layoutAux (Piece (f, len), _) =
    let
        val s = layoutAux (f, false)
    in
        "[" ^ (Int.toString len) ^ ": " ^ s ^ "]"
    end
  | layoutAux (Ap (e1, e2), ifp) =
    let
        val s = layoutAux (e1, true) ^ " " ^ (layoutAux (e2, true))
    in
        if ifp then paren s else s
    end
and layout func = layoutAux (func, true)

(* fun comp (f1, f2) = *)
(*     case f1 of *)
(*         C v => C v *)
(*       | X => f2 *)
(*       | Vector l => Vector (List.map (fn e => comp (e, f2)) l) *)
(*       | Nth (f1, i) => Nth (comp (f1, f2), i) *)
(*       | Add (f11, f12) => Add (comp (f11, f2), comp (f12, f2)) *)
(*       | Mul (f11, f12) => Mul (comp (f11, f2), comp (f12, f2)) *)
(*       | Fadd f1 => Fadd (comp (f1, f2)) *)
(*       | Map (f1, l) => Map (f1, comp (l, f2)) *)
(*       | Neg f => Neg (comp (f, f2)) *)
(*       | None => None *)
fun subst (body, id, v) =
    let
        fun aux body =
            case body of
                C v => C v
              | V x =>
                if x = id then v else V x
              | Vector l => Vector (List.map aux l)
              | Nth (l, i) => Nth (aux l, i)
              | Mul (e1, e2) => Mul (aux e1, aux e2)
              | Add (e1, e2) => Add (aux e1, aux e2)
              | Map (e1, e2) => Map (aux e1, aux e2)
              | Fadd e => Fadd (aux e)
              | Neg e => Neg (aux e)
              | Lam (x, body) =>
                if x = id then Lam (x, body) else Lam (x, aux body)
              | Ap (e1, e2) => Ap (aux e1, aux e2)
              | Piece (e, len) => Piece (subst (e, id, v), len)
              | None => None
    in
        aux body
    end
fun eval func =
    case func of
        C v => C v
      | V x => V x
      | Vector l => Vector (List.map eval l)
      | Nth (f1, i) =>
        (case eval f1 of
             Vector l => List.nth (l, i)
           | Piece (f, len) =>
             eval (Ap (f, C (Real.fromInt i)))
           | f1 => Nth (f1, i)
        )
      | Add (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 + v2)
           | (None, f2) => f2
           | (f1, None) => f1
           | (Vector f1, Vector f2) =>
             Vector (ListPair.map (fn (e1, e2) => eval (Add (e1, e2))) (f1, f2))
           | (Piece (f1, len1), Piece (f2, len2)) =>
             if len1 = len2
             then Piece (eval (Add (f1, f2)), len1)
             else raise Fail "Add Piece length error"
           | (f1, f2) => Add (f1, f2)
        )
      | Mul (f1, f2) =>
        (case (eval f1, eval f2) of
             (C v1, C v2) => C (v1 * v2)
           | (None, f2) => None
           | (f1, None) => None
           | (Vector f1, Vector f2) =>
             Vector (ListPair.map (fn (e1, e2) => eval (Mul (e1, e2))) (f1, f2))
           | (Piece (f1, len1), Piece (f2, len2)) =>
             if len1 = len2
             then Piece (eval (Mul (f1, f2)), len1)
             else raise Fail "Mul Piece length error"
           | (f1, f2) => Mul (f1, f2)
        )
      | Fadd f =>
        (case eval f of
             Vector f =>
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
          | Piece (f, len) =>
            eval (Fadd (Vector (List.tabulate (len, fn i => Ap (f, C (Real.fromInt i))))))
           | f => Fadd f
        )
      | Map (f, l) =>
        (case eval l of
             Vector l =>
             let
                 val r = List.map (fn e => Ap (f, e)) l
             in
                 eval (Vector r)
             end
           | Piece (fl, len) => Piece (Ap (f, fl), len)
           | l => Map (f,l)
        )
      | Neg f =>
        (case eval f of
             C v => C (~v)
           | None => None
           | Vector f => Vector (List.map eval f)
           | Piece (f, len) => Piece (eval (Neg f), len)
           | f => Neg f
        )
      | Lam (x, body) => Lam (x, eval body)
      | Ap (e1, e2) =>
        (case (eval e1, eval e2) of
             (Lam (x, body), v) => eval (subst (body, x, v))
           | (Piece (f, len), v) => eval (Ap (f, v))
           | _ => raise Fail "Ap error"
        )
      | Piece x => Piece x
      | None => None
fun hop (n, i, v) =
    let
        val none = List.tabulate (n, fn j => if i = j then v else None)
    in
        Vector none
    end
end


structure DPlus =
struct
open Func
fun slope func =
    let
        val v0 = eval (Ap (func, None))
        val v1 = eval (Ap (func, C 1.0))
    in
        case (v0, v1) of
            (C v0, C v1) => v1 - v0
         | _ => raise Fail "Bad slpoe"
    end
fun ad (func, x, v) =
    case func of
        C v => None
      | V y => if x = y then V x else None ∘
      | Vector l => Vector (List.map (fn e => ad (e, x, v)) l)
      | Piece (f, len) =>
        (case f of
             Lam (i, body) => Piece (Lam (x, Mul (C (slope func), V x)), len)
           | _ => raise Fail "Ad: bad Peice"
        )
      | Nth (f, i) => Nth (ad (f, x, v), i)
      | Add (f1, f2) => Add (ad (f1, x, v), ad (f2, x, v))
      | Mul (f1, f2) =>
        let
            val d1 = ad (f1, x, v)
            val v1 = eval (Ap (Lam (x, f1), v))
            val d2 = ad (f2, x, v)
            val v2 = eval (Ap (Lam (x, f2), v))
        in
            Add (Mul (v2, d1), Mul (v1, d2))
        end
      | Neg f => Neg (ad (f, x, v))
      | Fadd f => Fadd (ad (f, x, v))
      | Map (f, l) =>
        (case f of
             Lam (y, body) =>
             let
                 val d = ad (l, x, v)
                 val v' = eval (Ap (Lam (x, l), v))
                 val d' = ad (body, y, v')
             in
                 eval (Ap (Lam (y, d'), d))
             end
           | _ => raise Fail "map ad error"
        )
      | Lam (y, body) => Lam (y, body)
      | Ap (f, v) =>
        (case f of
             Lam (y, body) =>
             let
                 val d = ad (body, x, v)
                 val v' = eval (Ap (Lam (x, body), v))
                 val d' = ad (f, y, v')
             in
                 eval (Ap (Lam (y, d'), d))
             end
           | _ => raise Fail "ap ad error"
        )
      | None => None
fun adfunc (f, v) =
    case eval f of
        Lam (x, body) => Lam (x, ad (body, x, v))
      | _ => raise Fail "Bad ad"
                   (* fun toDiffAux (dom, i, func) = *)
                   (*     let *)
                   (*         val hop = hop (dom, i, X) *)
                   (*         val diff = comp (func X, hop) *)
                   (*         val y0 = comp (diff, None) *)
                   (*         val y1 = comp (diff, C 1.0) *)
                   (*         val diff = Add (y1, Neg y0) *)
                   (*     in *)
                   (*         eval diff *)
                   (*     end *)
                   (* fun toDiff {dom, codom, funcd = (_, func)} = *)
                   (*     let *)
                   (*         val result = List.tabulate (dom, fn i => i) *)
                   (*         val result = List.map (fn i => toDiffAux (dom, i, func)) result *)
                   (*     in *)
                   (*         result *)
                   (*     end *)
end;

(* structure D = *)
(* struct *)
(* structure F = Func *)
(* type dimension = int *)
(* type object = dimension *)
(* type arrow = {dom : object, codom : object, funcd: F.t * (F.t -> F.t)} *)
(* fun id dim = {dom = dim, codom = dim, funcd = (F.X, fn x => F.X)} *)
(* fun dom {dom, codom, funcd} = dom *)
(* fun codom {dom, codom, funcd} = codom *)
(* fun circ {dom = dom1, codom = codom1, funcd = (f1, fd1)} *)
(*          {dom = dom2, codom = codom2, funcd = (f2, fd2)} = *)
(*     let *)
(*         val _ = if codom2 = dom1 then () else print "domain does not match, can't compose1\n" *)
(*         val f = F.comp (f1, f2) *)
(*         fun d x = *)
(*             let *)
(*                 val y = F.comp (f2, x) *)
(*                 val linear2 = fd2 x *)
(*                 val linear1 = fd1 y *)
(*             in *)
(*                 F.comp (linear1, linear2) *)
(*             end *)
(*     in *)
(*         {dom = dom2, codom = codom1, funcd = (f, d)} *)
(*     end *)
(* fun layout {dom, codom, funcd = (f, d)} = *)
(*     let *)
(*         val ty = (Int.toString dom) ^ " ⇒ " ^ (Int.toString codom) *)
(*     in *)
(*         (F.layout (F.eval f)) ^ " ≈ " ^ (F.layout (F.eval (d F.X))) ^ ": " ^ ty *)
(*     end *)
(* fun new (dom, codom, func) = *)
(*     {dom = dom, codom = codom, funcd = (func, fn x => DPlus.ad (func, x))} *)
(* fun value (dom, func) = *)
(*     {dom = dom, codom = dom, funcd = (func, fn x => F.X)} *)
(* end; *)

open Func;
let
    val X = V "x"
    val arr1 = Lam ("x", Fadd (Mul (X, X)))
    val v1 = Vector [C 1.0, C 2.0, C 3.0, C 4.0]
    val _ = pLn (layout arr1)
    val d = DPlus.adfunc (arr1, v1)
    val _ = pLn (layout d)
    val arr2 = Piece (Lam ("i", Add (Mul (C 2.0, V "i"), C 1.0)), 4)
    val _ = pLn (layout arr2)
    val arr3 = Lam ("x", Ap (arr1, Ap (arr2, V "x")))
    val _ = pLn (layout arr3)
    val arr4 = eval arr3
    val _ = pLn (layout arr4)
    val d0 = DPlus.adfunc (arr3, C 1.0)
    val _ = pLn (layout d0)
in
    ()
end;
