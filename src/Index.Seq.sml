signature SEQUENCE =
sig
  type 'a seq
  
  val empty : 'a seq
  val cons : 'a * 'a seq -> 'a seq
  val snoc : 'a seq * 'a -> 'a seq
  val link : 'a seq * 'a seq -> 'a seq
  val uncons : 'a seq -> ('a * 'a seq) option
  val unsnoc : 'a seq -> ('a seq * 'a) option
  val size : 'a seq -> int
  
  type 'a hole
  
  val get : int * 'a seq -> ('a * 'a hole) option
  val set : 'a * 'a hole -> 'a seq
end

structure Sequence :> SEQUENCE =
struct
  datatype 'a tree
    = Leaf of 'a
    | Node2 of int * 'a tree * 'a tree
    | Node3 of int * 'a tree * 'a tree * 'a tree
  
  fun sizeT (Leaf _) = 1
    | sizeT (Node2 (n,_,_)) = n
    | sizeT (Node3 (n,_,_,_)) = n
  
  fun n2 (a,b) = Node2 (sizeT a + sizeT b, a, b)
  fun n3 (a,b,c) = Node3 (sizeT a + sizeT b + sizeT c, a, b, c)
  
  datatype 'a digit
    = D1 of 'a tree
    | D2 of 'a tree * 'a tree
    | D3 of 'a tree * 'a tree * 'a tree
    | D4 of 'a tree * 'a tree * 'a tree * 'a tree
  
  fun sizeF (D1 a) = sizeT a
    | sizeF (D2 (a,b)) = sizeT a + sizeT b
    | sizeF (D3 (a,b,c)) = sizeT a + sizeT b + sizeT c
    | sizeF (D4 (a,b,c,d)) = sizeT a + sizeT b + sizeT c + sizeT d
  
  fun ns2 (D1 a, D1 b) = D1 (n2 (a,b))
    | ns2 (D1 a, D2 (b,c)) = D1 (n3 (a,b,c))
    | ns2 (D2 (a,b), D1 c) = D1 (n3 (a,b,c))
    
    (*  N + N  *)
    | ns2 (D2 a, D2 b) = D2 (n2 a, n2 b)
    | ns2 (D2 a, D3 b) = D2 (n2 a, n3 b)
    | ns2 (D3 a, D2 b) = D2 (n3 a, n2 b)
    | ns2 (D3 a, D3 b) = D2 (n3 a, n3 b)
    
    (*  1 + 3  and  1 + 4  and 2 + 4  *)
    | ns2 (D3 (a,b,c), D1 d) = D2 (n2 (a,b), n2 (c,d))
    | ns2 (D1 a, D3 (b,c,d)) = D2 (n2 (a,b), n2 (c,d))
    | ns2 (D4 (a,b,c,d), D1 e) = D2 (n3 (a,b,c), n2 (d,e))
    | ns2 (D1 a, D4 (b,c,d,e)) = D2 (n3 (a,b,c), n2 (d,e))
    | ns2 (D4 (a,b,c,d), D2 (e,f)) = D2 (n3 (a,b,c), n3 (d,e,f))
    | ns2 (D2 (a,b), D4 (c,d,e,f)) = D2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  3 + 4  and  4 + 4  *)
    | ns2 (D4 (a,b,c,d), D3 e) = D3 (n2 (a,b), n2 (c,d), n3 e)
    | ns2 (D3 a, D4 (b,c,d,e)) = D3 (n3 a, n2 (b,c), n2 (d,e))
    | ns2 (D4 (a,b,c,d), D4 (e,f,g,h)) = D3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
  
  fun ns3 (D1 a, D1 b, D1 c) = D1 (n3 (a,b,c))
    
    (*  1 + 1 + [N]  *)
    | ns3 (D1 a, D1 b, D2 c) = D2 (n2 (a,b), n2 c)
    | ns3 (D1 a, D1 b, D3 c) = D2 (n2 (a,b), n3 c)
    | ns3 (D2 a, D1 b, D1 c) = D2 (n2 a, n2 (b,c))
    | ns3 (D3 a, D1 b, D1 c) = D2 (n3 a, n2 (b,c))
    
    (*  1 + 2 + [N]  *)
    | ns3 (D2 (a,b), D1 c, D2 d) = D2 (n3 (a,b,c), n2 d)
    | ns3 (D2 (a,b), D1 c, D3 d) = D2 (n3 (a,b,c), n3 d)
    | ns3 (D1 a, D2 (b,c), D2 d) = D2 (n3 (a,b,c), n2 d)
    | ns3 (D1 a, D2 (b,c), D3 d) = D2 (n3 (a,b,c), n3 d)
    | ns3 (D2 a, D2 (b,c), D1 d) = D2 (n2 a, n3 (b,c,d))
    | ns3 (D3 a, D1 b, D2 (c,d)) = D2 (n3 a, n3 (b,c,d))
    | ns3 (D3 a, D2 (b,c), D1 d) = D2 (n3 a, n3 (b,c,d))
    
    (*  1 + [N] + 1  *)
    | ns3 (D1 a, D2 (b,c), D1 d) = D2 (n2 (a,b), n2 (c,d))
    | ns3 (D1 a, D3 (b,c,d), D1 e) = D2 (n3 (a,b,c), n2 (d,e))
    
    (*  1 + 1 + 4  *)
    | ns3 (D4 (a,b,c,d), D1 e, D1 f) = D2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (D1 a, D4 (b,c,d,e), D1 f) = D2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (D1 a, D1 b, D4 (c,d,e,f)) = D2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  F + F + [2] = 6  *)
    | ns3 (D2 (a,b), D3 (c,d,e), D1 f) = D2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (D1 a, D3 (b,c,d), D2 (e,f)) = D2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (D2 (a,b), D2 (c,d), D2 (e,f)) = D2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  N + N + N  except  2 + 2 + 2  *)
    | ns3 (D2 a, D2 b, D3 c) = D3 (n2 a, n2 b, n3 c)
    | ns3 (D2 a, D3 b, D2 c) = D3 (n2 a, n3 b, n2 c)
    | ns3 (D2 a, D3 b, D3 c) = D3 (n2 a, n3 b, n3 c)
    | ns3 (D3 a, D2 b, D2 c) = D3 (n3 a, n2 b, n2 c)
    | ns3 (D3 a, D2 b, D3 c) = D3 (n3 a, n2 b, n3 c)
    | ns3 (D3 a, D3 b, D2 c) = D3 (n3 a, n3 b, n2 c)
    | ns3 (D3 a, D3 b, D3 c) = D3 (n3 a, n3 b, n3 c)
    
    (*  1 + 4 + [N]  *)
    | ns3 (D4 (a,b,c,d), D1 e, D2 f) = D3 (n3 (a,b,c), n2 (d,e), n2 f)
    | ns3 (D4 (a,b,c,d), D1 e, D3 f) = D3 (n3 (a,b,c), n2 (d,e), n3 f)
    | ns3 (D1 a, D4 (b,c,d,e), D2 f) = D3 (n3 (a,b,c), n2 (d,e), n2 f)
    | ns3 (D1 a, D4 (b,c,d,e), D3 f) = D3 (n3 (a,b,c), n2 (d,e), n3 f)
    | ns3 (D2 a, D4 (b,c,d,e), D1 f) = D3 (n2 a, n2 (b,c), n3 (d,e,f))
    | ns3 (D3 a, D4 (b,c,d,e), D1 f) = D3 (n3 a, n2 (b,c), n3 (d,e,f))
    | ns3 (D2 a, D1 b, D4 (c,d,e,f)) = D3 (n2 a, n2 (b,c), n3 (d,e,f))
    | ns3 (D3 a, D1 b, D4 (c,d,e,f)) = D3 (n3 a, n2 (b,c), n3 (d,e,f))
    
    (*  1 + [N] + 4  *)
    | ns3 (D4 (a,b,c,d), D2 (e,f), D1 g) = D3 (n3 (a,b,c), n2 (d,e), n2 (f,g))
    | ns3 (D1 a, D2 (b,c), D4 (d,e,f,g)) = D3 (n3 (a,b,c), n2 (d,e), n2 (f,g))
    | ns3 (D4 (a,b,c,d), D3 (e,f,g), D1 h) = D3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
    | ns3 (D1 a, D3 (b,c,d), D4 (e,f,g,h)) = D3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
    
    (*  1 + 3 + 3  *)
    | ns3 (D1 a, D3 (b,c,d), D3 e) = D3 (n2 (a,b), n2 (c,d), n3 e)
    | ns3 (D3 a, D3 (b,c,d), D1 e) = D3 (n3 a, n2 (b,c), n2 (d,e))
    | ns3 (D3 a, D1 b, D3 (c,d,e)) = D3 (n3 a, n2 (b,c), n2 (d,e))
    
    (*  2 + 4 + [N]  *)
    | ns3 (D4 (a,b,c,d), D2 (e,f), D2 g) = D3 (n3 (a,b,c), n3 (d,e,f), n2 g)
    | ns3 (D4 (a,b,c,d), D2 (e,f), D3 g) = D3 (n3 (a,b,c), n3 (d,e,f), n3 g)
    | ns3 (D2 (a,b), D4 (c,d,e,f), D2 g) = D3 (n3 (a,b,c), n3 (d,e,f), n2 g)
    | ns3 (D2 (a,b), D4 (c,d,e,f), D3 g) = D3 (n3 (a,b,c), n3 (d,e,f), n3 g)
    | ns3 (D2 a, D2 (b,c), D4 (d,e,f,g)) = D3 (n2 a, n3 (b,c,d), n3 (e,f,g))
    | ns3 (D3 a, D2 (b,c), D4 (d,e,f,g)) = D3 (n3 a, n3 (b,c,d), n3 (e,f,g))
    | ns3 (D3 a, D4 (b,c,d,e), D2 (f,g)) = D3 (n3 a, n3 (b,c,d), n3 (e,f,g))
    
    (*  F + F + [4] = 9  except  3 + [2] + 4  *)
    | ns3 (D1 a, D4 (b,c,d,e), D4 (f,g,h,i)) = D3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (D4 (a,b,c,d), D1 e, D4 (f,g,h,i)) = D3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (D4 (a,b,c,d), D4 (e,f,g,h), D1 i) = D3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (D4 (a,b,c,d), D3 (e,f,g), D2 (h,i)) = D3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (D2 (a,b), D3 (c,d,e), D4 (f,g,h,i)) = D3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    
    (*  3 + 3 + 4  *)
    | ns3 (D4 (a,b,c,d), D3 e, D3 f) = D4 (n2 (a,b), n2 (c,d), n3 e, n3 f)
    | ns3 (D3 a, D4 (b,c,d,e), D3 f) = D4 (n3 a, n2 (b,c), n2 (d,e), n3 f)
    | ns3 (D3 a, D3 b, D4 (c,d,e,f)) = D4 (n3 a, n3 b, n2 (c,d), n2 (e,f))
    
    (*  4 + 4 + [N]  *)
    | ns3 (D4 (a,b,c,d), D4 (e,f,g,h), D2 i) = D4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n2 i)
    | ns3 (D4 (a,b,c,d), D4 (e,f,g,h), D3 i) = D4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n3 i)
    | ns3 (D2 a, D4 (b,c,d,e), D4 (f,g,h,i)) = D4 (n2 a, n2 (b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (D3 a, D4 (b,c,d,e), D4 (f,g,h,i)) = D4 (n3 a, n2 (b,c), n3 (d,e,f), n3 (g,h,i))
    
    (*  4 + [F] + 4  except  4 + [1] + 4  *)
    | ns3 (D4 (a,b,c,d), D2 (e,f), D4 (g,h,i,j)) = D4 (n3 (a,b,c), n2 (d,e), n2 (f,g), n3 (h,i,j))
    | ns3 (D4 (a,b,c,d), D3 (e,f,g), D4 (h,i,j,k)) = D4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n3 (i,j,k))
    | ns3 (D4 (a,b,c,d), D4 (e,f,g,h), D4 (i,j,k,l)) = D4 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i), n3 (j,k,l))
  
  datatype 'a seq
    = Empty
    | Pure of 'a tree
    | Cons of 'a tree * 'a seq ref
    | Snoc of 'a seq ref * 'a tree
    | LinkL of 'a seq ref * 'a digit * 'a seq ref
    | LinkR of 'a seq * 'a digit * 'a seq ref
    | Uncons of int * 'a seq ref * 'a digit
    | Unsnoc of int * 'a digit * 'a seq ref
    | Many of int * 'a digit * 'a seq ref * 'a digit
  
  fun size (Many (m, xs, _, ys)) = m + sizeF xs  + sizeF ys
    | size (Pure x) = sizeT x
    | size _ = 0
  
  fun few (D1 x) = Pure x
    | few (D2 (x,y)) = Many (0, D1 x, ref Empty, D1 y)
    | few (D3 (x,y,z)) = Many (0, D2 (x,y), ref Empty, D1 z)
    | few (D4 (x,y,z,w)) = Many (0, D2 (x,y), ref Empty, D2 (z,w))
  
  fun consT (a, Many (n, D4 (b,c,d,e), xs, ys)) =
      let
        val m = sizeT c + sizeT d + sizeT e
        val x = Node3 (m,c,d,e)
      in
        Many (n + m, D2 (a,b), ref (Cons (x, xs)), ys)
      end
    
    | consT (a, Many (n, D3 (b,c,d), xs, ys)) = Many (n, D4 (a,b,c,d), xs, ys)
    | consT (a, Many (n, D2 (b,c), xs, ys)) = Many (n, D3 (a,b,c), xs, ys)
    | consT (a, Many (n, D1 b, xs, ys)) = Many (n, D2 (a,b), xs, ys)
    | consT (a, Pure b) = Many (0, D1 a, ref Empty, D1 b)
    | consT (x, _) = Pure x
  
  fun snocT (Many (n, xs, ys, D4 (a,b,c,d)), e) =
      let
        val m = sizeT a + sizeT b + sizeT c
        val y = Node3 (m,a,b,c)
      in
        Many (n + m, xs, ref (Snoc (ys, y)), D2 (d,e))
      end
    
    | snocT (Many (n, xs, ys, D3 (a,b,c)), d) = Many (n, xs, ys, D4 (a,b,c,d))
    | snocT (Many (n, xs, ys, D2 (a,b)), c) = Many (n, xs, ys, D3 (a,b,c))
    | snocT (Many (n, xs, ys, D1 a), b) = Many (n, xs, ys, D2 (a,b))
    | snocT (Pure a, b) = Many (0, D1 a, ref Empty, D1 b)
    | snocT (_, x) = Pure x
  
  fun consF (D1 a, xs) = consT (a, xs)
    | consF (D2 (a,b), xs) = consT (a, consT (b, xs))
    | consF (D3 (a,b,c), xs) = consT (a, consT (b, consT (c, xs)))
    | consF (D4 (a,b,c,d), xs) = consT (a, consT (b, consT (c, consT (d, xs))))
  
  fun snocF (xs, D1 a) = snocT (xs, a)
    | snocF (xs, D2 (a,b)) = snocT (snocT (xs, a), b)
    | snocF (xs, D3 (a,b,c)) = snocT (snocT (snocT (xs, a), b), c)
    | snocF (xs, D4 (a,b,c,d)) = snocT (snocT (snocT (snocT (xs, a), b), c), d)
  
  fun unconsT (Many (n, D4 (a,b,c,d), xs, ys)) = SOME (a, Many (n, D3 (b,c,d), xs, ys))
    | unconsT (Many (n, D3 (a,b,c), xs, ys)) = SOME (a, Many (n, D2 (b,c), xs, ys))
    | unconsT (Many (n, D2 (a,b), xs, ys)) = SOME (a, Many (n, D1 b, xs, ys))
    | unconsT (Many (n, D1 a, xs, ys)) = SOME (a, Uncons (n, xs, ys))
    | unconsT (Pure x) = SOME (x, Empty)
    | unconsT _ = NONE
  
  fun unsnocT (Many (n, xs, ys, D4 (a,b,c,d))) = SOME (Many (n, xs, ys, D3 (a,b,c)), d)
    | unsnocT (Many (n, xs, ys, D3 (a,b,c))) = SOME (Many (n, xs, ys, D2 (a,b)), c)
    | unsnocT (Many (n, xs, ys, D2 (a,b))) = SOME (Many (n, xs, ys, D1 a), b)
    | unsnocT (Many (n, xs, ys, D1 a)) = SOME (Unsnoc (n, xs, ys), a)
    | unsnocT (Pure x) = SOME (Empty, x)
    | unsnocT _ = NONE
  
  fun unconsF (n, xs, ys) =
    case unconsT xs of
        SOME (Node3 (m,a,b,c), xs) => Many (n - m, D3 (a,b,c), ref xs, ys)
      | SOME (Node2 (m,a,b), xs) => Many (n - m, D2 (a,b), ref xs, ys)
      | _ => few ys
  
  fun unsnocF (n, xs, ys) =
    case unsnocT ys of
        SOME (ys, Node3 (m,a,b,c)) => Many (n - m, xs, ref ys, D3 (a,b,c))
      | SOME (ys, Node2 (m,a,b)) => Many (n - m, xs, ref ys, D2 (a,b))
      | _ => few xs
  
  fun link (Many (m,a,b,c), Many (n,d,e,f)) =
      let val x = ns2 (c,d)
      in Many (m + n + sizeF x, a, ref (LinkL (b,x,e)), f) end
    
    | link (Pure x, xs) = consT (x, xs)
    | link (xs, Pure x) = snocT (xs, x)
    | link (Empty, xs) = xs
    | link (xs, _) = xs
  
  fun link3 (Many (m,a,b,c), d, Many (n,e,f,g)) =
      let val x = ns3 (c,d,e)
      in Many (m + n + sizeF x, a, ref (LinkL (b,x,f)), g) end
    
    | link3 (Pure x, xs, xss) = consT (x, consF (xs, xss))
    | link3 (xss, xs, Pure x) = snocT (snocF (xss, xs), x)
    | link3 (Empty, x, xs) = consF (x, xs)
    | link3 (xs, x, _) = snocF (xs, x)
  
  fun run (Cons (x,r), ss) = run (!r, Cons (x,r) :: ss)
    | run (Snoc (r,x), ss) = run (!r, Snoc (r,x) :: ss)
    | run (Uncons (n,r,x), ss) = run (!r, Uncons (n,r,x) :: ss)
    | run (Unsnoc (n,x,r), ss) = run (!r, Unsnoc (n,x,r) :: ss)
    | run (LinkL (r,x,s), ss) = run (!r, LinkL (r,x,s) :: ss)
    | run (LinkR (x,y,r), ss) = run (!r, LinkR (x,y,r) :: ss)
    | run (y, Cons (x,r) :: ss) = (r := y; run (consT (x,y), ss))
    | run (x, Snoc (r,y) :: ss) = (r := x; run (snocT (x,y), ss))
    | run (x, Uncons (n,r,y) :: ss) = (r := x; run (unconsF (n,x,y), ss))
    | run (y, Unsnoc (n,x,r) :: ss) = (r := y; run (unsnocF (n,x,y), ss))
    | run (x, LinkL (r,y,z) :: ss) = (r := x; run (LinkR (x,y,z), ss))
    | run (z, LinkR (x,y,r) :: ss) = (r := z; run (link3 (x,y,z), ss))
    | run (x, _) = x
  
  val empty = Empty
  fun cons (x, xs) = consT (Leaf x, xs)
  fun snoc (xs, x) = snocT (xs, Leaf x)
  fun force xs = run (xs, nil)
  
  fun uncons xs =
    case unconsT xs of
        SOME (Leaf x, xs) => SOME (x, force xs)
      | _ => NONE
  
  fun unsnoc xs =
    case unsnocT xs of
        SOME (xs, Leaf x) => SOME (force xs, x)
      | _ => NONE
  
  datatype 'a step
    = T11
    | T21 of 'a tree
    | T22 of 'a tree
    | T31 of 'a tree * 'a tree
    | T32 of 'a tree * 'a tree
    | T33 of 'a tree * 'a tree
    | T41 of 'a tree * 'a tree * 'a tree
    | T42 of 'a tree * 'a tree * 'a tree
    | T43 of 'a tree * 'a tree * 'a tree
    | T44 of 'a tree * 'a tree * 'a tree
    | L of int * 'a seq ref * 'a digit
    | R of int * 'a digit * 'a seq ref
    | M of 'a digit * 'a digit
  
  type 'a hole = 'a step list
  
  fun seq (ys, M (xs, zs) :: ss) = seq (Many (size ys, xs, ref ys, zs), ss)
    | seq (xs, _) = xs
  
  fun tree (a, T41 (b,c,d) :: L (m, xs, ys) :: ss) = seq (Many (m, D4 (a,b,c,d), xs, ys), ss)
    | tree (b, T42 (a,c,d) :: L (m, xs, ys) :: ss) = seq (Many (m, D4 (a,b,c,d), xs, ys), ss)
    | tree (c, T43 (a,b,d) :: L (m, xs, ys) :: ss) = seq (Many (m, D4 (a,b,c,d), xs, ys), ss)
    | tree (d, T44 (a,b,c) :: L (m, xs, ys) :: ss) = seq (Many (m, D4 (a,b,c,d), xs, ys), ss)
    | tree (a, T41 (b,c,d) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D4 (a,b,c,d)), ss)
    | tree (b, T42 (a,c,d) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D4 (a,b,c,d)), ss)
    | tree (c, T43 (a,b,d) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D4 (a,b,c,d)), ss)
    | tree (d, T44 (a,b,c) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D4 (a,b,c,d)), ss)
    | tree (a, T31 (b,c) :: L (m, xs, ys) :: ss) = seq (Many (m, D3 (a,b,c), xs, ys), ss)
    | tree (b, T32 (a,c) :: L (m, xs, ys) :: ss) = seq (Many (m, D3 (a,b,c), xs, ys), ss)
    | tree (c, T33 (a,b) :: L (m, xs, ys) :: ss) = seq (Many (m, D3 (a,b,c), xs, ys), ss)
    | tree (a, T31 (b,c) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D3 (a,b,c)), ss)
    | tree (b, T32 (a,c) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D3 (a,b,c)), ss)
    | tree (c, T33 (a,b) :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D3 (a,b,c)), ss)
    | tree (a, T21 b :: L (m, xs, ys) :: ss) = seq (Many (m, D2 (a,b), xs, ys), ss)
    | tree (b, T22 a :: L (m, xs, ys) :: ss) = seq (Many (m, D2 (a,b), xs, ys), ss)
    | tree (a, T21 b :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D2 (a,b)), ss)
    | tree (b, T22 a :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D2 (a,b)), ss)
    | tree (a, T11 :: L (m, xs, ys) :: ss) = seq (Many (m, D1 a, xs, ys), ss)
    | tree (a, T11 :: R (m, xs, ys) :: ss) = seq (Many (m, xs, ys, D1 a), ss)
    | tree (a, T31 (b,c) :: ss) = tree (n3 (a,b,c), ss)
    | tree (b, T32 (a,c) :: ss) = tree (n3 (a,b,c), ss)
    | tree (c, T33 (a,b) :: ss) = tree (n3 (a,b,c), ss)
    | tree (a, T21 b :: ss) = tree (n2 (a,b), ss)
    | tree (b, T22 a :: ss) = tree (n2 (a,b), ss)
    | tree (x, ss) = seq (Pure x, ss)
  
  fun set (x, ss) = tree (Leaf x, ss)
  
  datatype 'a try
    = Tree of 'a tree * 'a hole
    | Digit of 'a digit * 'a hole
    | Force of int * 'a seq ref * 'a hole
    | Seq of 'a seq * 'a hole
  
  fun find (m, Force (n, r, ss) :: ts) =
      if m < n then
        let val xs = force (!r)
        in r := xs; find (m, Seq (xs, ss) :: nil) end
      else
        find (m - n, ts)
    
    | find (m, Seq (Pure x, ss) :: _) = find (m, Tree (x, ss) :: nil)
    | find (m, Seq (Many (n, xs, ys, zs), ss) :: _) =
      find (m, Digit (xs, L (m, ys, zs) :: ss) ::
               Force (n, ys, M (xs, zs) :: ss) ::
               Digit (zs, R (m, xs, ys) :: ss) :: nil)
    
    | find (m, Digit (D1 a, ss) :: ts) =
      find (m, Tree (a, T11 :: ss) :: ts)
    
    | find (m, Digit (D2 (a,b), ss) :: ts) =
      find (m, Tree (a, T21 b :: ss) ::
               Tree (b, T22 a :: ss) :: ts)
    
    | find (m, Digit (D3 (a,b,c), ss) :: ts) =
      find (m, Tree (a, T31 (b,c) :: ss) ::
               Tree (b, T32 (a,c) :: ss) ::
               Tree (c, T33 (a,b) :: ss) :: ts)
    
    | find (m, Digit (D4 (a,b,c,d), ss) :: ts) =
      find (m, Tree (a, T41 (b,c,d) :: ss) ::
               Tree (b, T42 (a,c,d) :: ss) ::
               Tree (c, T43 (a,b,d) :: ss) ::
               Tree (d, T44 (a,b,c) :: ss) :: ts)
    
    | find (0, Tree (Leaf x, ss) :: _) = SOME (x, ss)
    | find (m, Tree (Leaf _, _) :: ts) = find (m - 1, ts)
    | find (m, Tree (Node2 (n,a,b), ss) :: ts) =
      if m < n then
        find (m, Tree (a, T21 b :: ss) ::
                 Tree (b, T22 a :: ss) :: nil)
      else
        find (m - n, ts)
    
    | find (m, Tree (Node3 (n,a,b,c), ss) :: ts) =
      if m < n then
        find (m, Tree (a, T31 (b,c) :: ss) ::
                 Tree (b, T32 (a,c) :: ss) ::
                 Tree (c, T33 (a,b) :: ss) :: nil)
      else
        find (m - n, ts)
    
    | find _ = NONE
  
  fun get (n, xs) = if n >= 0 then find (n, Seq (xs, nil) :: nil) else NONE
end
