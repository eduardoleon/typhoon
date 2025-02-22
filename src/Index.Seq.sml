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
  
  datatype 'a finger
    = F1 of 'a tree
    | F2 of 'a tree * 'a tree
    | F3 of 'a tree * 'a tree * 'a tree
    | F4 of 'a tree * 'a tree * 'a tree * 'a tree
  
  fun sizeF (F1 a) = sizeT a
    | sizeF (F2 (a,b)) = sizeT a + sizeT b
    | sizeF (F3 (a,b,c)) = sizeT a + sizeT b + sizeT c
    | sizeF (F4 (a,b,c,d)) = sizeT a + sizeT b + sizeT c + sizeT d
  
  fun ns2 (F1 a, F1 b) = F1 (n2 (a,b))
    | ns2 (F1 a, F2 (b,c)) = F1 (n3 (a,b,c))
    | ns2 (F2 (a,b), F1 c) = F1 (n3 (a,b,c))
    
    (*  N + N  *)
    | ns2 (F2 a, F2 b) = F2 (n2 a, n2 b)
    | ns2 (F2 a, F3 b) = F2 (n2 a, n3 b)
    | ns2 (F3 a, F2 b) = F2 (n3 a, n2 b)
    | ns2 (F3 a, F3 b) = F2 (n3 a, n3 b)
    
    (*  1 + 3  and  1 + 4  and 2 + 4  *)
    | ns2 (F3 (a,b,c), F1 d) = F2 (n2 (a,b), n2 (c,d))
    | ns2 (F1 a, F3 (b,c,d)) = F2 (n2 (a,b), n2 (c,d))
    | ns2 (F4 (a,b,c,d), F1 e) = F2 (n3 (a,b,c), n2 (d,e))
    | ns2 (F1 a, F4 (b,c,d,e)) = F2 (n3 (a,b,c), n2 (d,e))
    | ns2 (F4 (a,b,c,d), F2 (e,f)) = F2 (n3 (a,b,c), n3 (d,e,f))
    | ns2 (F2 (a,b), F4 (c,d,e,f)) = F2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  3 + 4  and  4 + 4  *)
    | ns2 (F4 (a,b,c,d), F3 e) = F3 (n2 (a,b), n2 (c,d), n3 e)
    | ns2 (F3 a, F4 (b,c,d,e)) = F3 (n3 a, n2 (b,c), n2 (d,e))
    | ns2 (F4 (a,b,c,d), F4 (e,f,g,h)) = F3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
  
  fun ns3 (F1 a, F1 b, F1 c) = F1 (n3 (a,b,c))
    
    (*  1 + 1 + [N]  *)
    | ns3 (F1 a, F1 b, F2 c) = F2 (n2 (a,b), n2 c)
    | ns3 (F1 a, F1 b, F3 c) = F2 (n2 (a,b), n3 c)
    | ns3 (F2 a, F1 b, F1 c) = F2 (n2 a, n2 (b,c))
    | ns3 (F3 a, F1 b, F1 c) = F2 (n3 a, n2 (b,c))
    
    (*  1 + 2 + [N]  *)
    | ns3 (F2 (a,b), F1 c, F2 d) = F2 (n3 (a,b,c), n2 d)
    | ns3 (F2 (a,b), F1 c, F3 d) = F2 (n3 (a,b,c), n3 d)
    | ns3 (F1 a, F2 (b,c), F2 d) = F2 (n3 (a,b,c), n2 d)
    | ns3 (F1 a, F2 (b,c), F3 d) = F2 (n3 (a,b,c), n3 d)
    | ns3 (F2 a, F2 (b,c), F1 d) = F2 (n2 a, n3 (b,c,d))
    | ns3 (F3 a, F1 b, F2 (c,d)) = F2 (n3 a, n3 (b,c,d))
    | ns3 (F3 a, F2 (b,c), F1 d) = F2 (n3 a, n3 (b,c,d))
    
    (*  1 + [N] + 1  *)
    | ns3 (F1 a, F2 (b,c), F1 d) = F2 (n2 (a,b), n2 (c,d))
    | ns3 (F1 a, F3 (b,c,d), F1 e) = F2 (n3 (a,b,c), n2 (d,e))
    
    (*  1 + 1 + 4  *)
    | ns3 (F4 (a,b,c,d), F1 e, F1 f) = F2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (F1 a, F4 (b,c,d,e), F1 f) = F2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (F1 a, F1 b, F4 (c,d,e,f)) = F2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  F + F + [2] = 6  *)
    | ns3 (F2 (a,b), F3 (c,d,e), F1 f) = F2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (F1 a, F3 (b,c,d), F2 (e,f)) = F2 (n3 (a,b,c), n3 (d,e,f))
    | ns3 (F2 (a,b), F2 (c,d), F2 (e,f)) = F2 (n3 (a,b,c), n3 (d,e,f))
    
    (*  N + N + N  except  2 + 2 + 2  *)
    | ns3 (F2 a, F2 b, F3 c) = F3 (n2 a, n2 b, n3 c)
    | ns3 (F2 a, F3 b, F2 c) = F3 (n2 a, n3 b, n2 c)
    | ns3 (F2 a, F3 b, F3 c) = F3 (n2 a, n3 b, n3 c)
    | ns3 (F3 a, F2 b, F2 c) = F3 (n3 a, n2 b, n2 c)
    | ns3 (F3 a, F2 b, F3 c) = F3 (n3 a, n2 b, n3 c)
    | ns3 (F3 a, F3 b, F2 c) = F3 (n3 a, n3 b, n2 c)
    | ns3 (F3 a, F3 b, F3 c) = F3 (n3 a, n3 b, n3 c)
    
    (*  1 + 4 + [N]  *)
    | ns3 (F4 (a,b,c,d), F1 e, F2 f) = F3 (n3 (a,b,c), n2 (d,e), n2 f)
    | ns3 (F4 (a,b,c,d), F1 e, F3 f) = F3 (n3 (a,b,c), n2 (d,e), n3 f)
    | ns3 (F1 a, F4 (b,c,d,e), F2 f) = F3 (n3 (a,b,c), n2 (d,e), n2 f)
    | ns3 (F1 a, F4 (b,c,d,e), F3 f) = F3 (n3 (a,b,c), n2 (d,e), n3 f)
    | ns3 (F2 a, F4 (b,c,d,e), F1 f) = F3 (n2 a, n2 (b,c), n3 (d,e,f))
    | ns3 (F3 a, F4 (b,c,d,e), F1 f) = F3 (n3 a, n2 (b,c), n3 (d,e,f))
    | ns3 (F2 a, F1 b, F4 (c,d,e,f)) = F3 (n2 a, n2 (b,c), n3 (d,e,f))
    | ns3 (F3 a, F1 b, F4 (c,d,e,f)) = F3 (n3 a, n2 (b,c), n3 (d,e,f))
    
    (*  1 + [N] + 4  *)
    | ns3 (F4 (a,b,c,d), F2 (e,f), F1 g) = F3 (n3 (a,b,c), n2 (d,e), n2 (f,g))
    | ns3 (F1 a, F2 (b,c), F4 (d,e,f,g)) = F3 (n3 (a,b,c), n2 (d,e), n2 (f,g))
    | ns3 (F4 (a,b,c,d), F3 (e,f,g), F1 h) = F3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
    | ns3 (F1 a, F3 (b,c,d), F4 (e,f,g,h)) = F3 (n3 (a,b,c), n2 (d,e), n3 (f,g,h))
    
    (*  1 + 3 + 3  *)
    | ns3 (F1 a, F3 (b,c,d), F3 e) = F3 (n2 (a,b), n2 (c,d), n3 e)
    | ns3 (F3 a, F3 (b,c,d), F1 e) = F3 (n3 a, n2 (b,c), n2 (d,e))
    | ns3 (F3 a, F1 b, F3 (c,d,e)) = F3 (n3 a, n2 (b,c), n2 (d,e))
    
    (*  2 + 4 + [N]  *)
    | ns3 (F4 (a,b,c,d), F2 (e,f), F2 g) = F3 (n3 (a,b,c), n3 (d,e,f), n2 g)
    | ns3 (F4 (a,b,c,d), F2 (e,f), F3 g) = F3 (n3 (a,b,c), n3 (d,e,f), n3 g)
    | ns3 (F2 (a,b), F4 (c,d,e,f), F2 g) = F3 (n3 (a,b,c), n3 (d,e,f), n2 g)
    | ns3 (F2 (a,b), F4 (c,d,e,f), F3 g) = F3 (n3 (a,b,c), n3 (d,e,f), n3 g)
    | ns3 (F2 a, F2 (b,c), F4 (d,e,f,g)) = F3 (n2 a, n3 (b,c,d), n3 (e,f,g))
    | ns3 (F3 a, F2 (b,c), F4 (d,e,f,g)) = F3 (n3 a, n3 (b,c,d), n3 (e,f,g))
    | ns3 (F3 a, F4 (b,c,d,e), F2 (f,g)) = F3 (n3 a, n3 (b,c,d), n3 (e,f,g))
    
    (*  F + F + [4] = 9  except  3 + [2] + 4  *)
    | ns3 (F1 a, F4 (b,c,d,e), F4 (f,g,h,i)) = F3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (F4 (a,b,c,d), F1 e, F4 (f,g,h,i)) = F3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (F4 (a,b,c,d), F4 (e,f,g,h), F1 i) = F3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (F4 (a,b,c,d), F3 (e,f,g), F2 (h,i)) = F3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (F2 (a,b), F3 (c,d,e), F4 (f,g,h,i)) = F3 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i))
    
    (*  3 + 3 + 4  *)
    | ns3 (F4 (a,b,c,d), F3 e, F3 f) = F4 (n2 (a,b), n2 (c,d), n3 e, n3 f)
    | ns3 (F3 a, F4 (b,c,d,e), F3 f) = F4 (n3 a, n2 (b,c), n2 (d,e), n3 f)
    | ns3 (F3 a, F3 b, F4 (c,d,e,f)) = F4 (n3 a, n3 b, n2 (c,d), n2 (e,f))
    
    (*  4 + 4 + [N]  *)
    | ns3 (F4 (a,b,c,d), F4 (e,f,g,h), F2 i) = F4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n2 i)
    | ns3 (F4 (a,b,c,d), F4 (e,f,g,h), F3 i) = F4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n3 i)
    | ns3 (F2 a, F4 (b,c,d,e), F4 (f,g,h,i)) = F4 (n2 a, n2 (b,c), n3 (d,e,f), n3 (g,h,i))
    | ns3 (F3 a, F4 (b,c,d,e), F4 (f,g,h,i)) = F4 (n3 a, n2 (b,c), n3 (d,e,f), n3 (g,h,i))
    
    (*  4 + [F] + 4  except  4 + [1] + 4  *)
    | ns3 (F4 (a,b,c,d), F2 (e,f), F4 (g,h,i,j)) = F4 (n3 (a,b,c), n2 (d,e), n2 (f,g), n3 (h,i,j))
    | ns3 (F4 (a,b,c,d), F3 (e,f,g), F4 (h,i,j,k)) = F4 (n3 (a,b,c), n3 (d,e,f), n2 (g,h), n3 (i,j,k))
    | ns3 (F4 (a,b,c,d), F4 (e,f,g,h), F4 (i,j,k,l)) = F4 (n3 (a,b,c), n3 (d,e,f), n3 (g,h,i), n3 (j,k,l))
  
  datatype 'a seq
    = Empty
    | Pure of 'a tree
    | Cons of 'a tree * 'a seq ref
    | Snoc of 'a seq ref * 'a tree
    | LinkL of 'a seq ref * 'a finger * 'a seq ref
    | LinkR of 'a seq * 'a finger * 'a seq ref
    | Uncons of int * 'a seq ref * 'a finger
    | Unsnoc of int * 'a finger * 'a seq ref
    | Many of int * 'a finger * 'a seq ref * 'a finger
  
  fun size (Many (m, xs, _, ys)) = m + sizeF xs  + sizeF ys
    | size (Pure x) = sizeT x
    | size _ = 0
  
  fun few (F1 x) = Pure x
    | few (F2 (x,y)) = Many (0, F1 x, ref Empty, F1 y)
    | few (F3 (x,y,z)) = Many (0, F2 (x,y), ref Empty, F1 z)
    | few (F4 (x,y,z,w)) = Many (0, F2 (x,y), ref Empty, F2 (z,w))
  
  fun consT (a, Many (n, F4 (b,c,d,e), xs, ys)) =
      let
        val m = sizeT c + sizeT d + sizeT e
        val x = Node3 (m,c,d,e)
      in
        Many (n + m, F2 (a,b), ref (Cons (x, xs)), ys)
      end
    
    | consT (a, Many (n, F3 (b,c,d), xs, ys)) = Many (n, F4 (a,b,c,d), xs, ys)
    | consT (a, Many (n, F2 (b,c), xs, ys)) = Many (n, F3 (a,b,c), xs, ys)
    | consT (a, Many (n, F1 b, xs, ys)) = Many (n, F2 (a,b), xs, ys)
    | consT (a, Pure b) = Many (0, F1 a, ref Empty, F1 b)
    | consT (x, _) = Pure x
  
  fun snocT (Many (n, xs, ys, F4 (a,b,c,d)), e) =
      let
        val m = sizeT a + sizeT b + sizeT c
        val y = Node3 (m,a,b,c)
      in
        Many (n + m, xs, ref (Snoc (ys, y)), F2 (d,e))
      end
    
    | snocT (Many (n, xs, ys, F3 (a,b,c)), d) = Many (n, xs, ys, F4 (a,b,c,d))
    | snocT (Many (n, xs, ys, F2 (a,b)), c) = Many (n, xs, ys, F3 (a,b,c))
    | snocT (Many (n, xs, ys, F1 a), b) = Many (n, xs, ys, F2 (a,b))
    | snocT (Pure a, b) = Many (0, F1 a, ref Empty, F1 b)
    | snocT (_, x) = Pure x
  
  fun consF (F1 a, xs) = consT (a, xs)
    | consF (F2 (a,b), xs) = consT (a, consT (b, xs))
    | consF (F3 (a,b,c), xs) = consT (a, consT (b, consT (c, xs)))
    | consF (F4 (a,b,c,d), xs) = consT (a, consT (b, consT (c, consT (d, xs))))
  
  fun snocF (xs, F1 a) = snocT (xs, a)
    | snocF (xs, F2 (a,b)) = snocT (snocT (xs, a), b)
    | snocF (xs, F3 (a,b,c)) = snocT (snocT (snocT (xs, a), b), c)
    | snocF (xs, F4 (a,b,c,d)) = snocT (snocT (snocT (snocT (xs, a), b), c), d)
  
  fun unconsT (Many (n, F4 (a,b,c,d), xs, ys)) = SOME (a, Many (n, F3 (b,c,d), xs, ys))
    | unconsT (Many (n, F3 (a,b,c), xs, ys)) = SOME (a, Many (n, F2 (b,c), xs, ys))
    | unconsT (Many (n, F2 (a,b), xs, ys)) = SOME (a, Many (n, F1 b, xs, ys))
    | unconsT (Many (n, F1 a, xs, ys)) = SOME (a, Uncons (n, xs, ys))
    | unconsT (Pure x) = SOME (x, Empty)
    | unconsT _ = NONE
  
  fun unsnocT (Many (n, xs, ys, F4 (a,b,c,d))) = SOME (Many (n, xs, ys, F3 (a,b,c)), d)
    | unsnocT (Many (n, xs, ys, F3 (a,b,c))) = SOME (Many (n, xs, ys, F2 (a,b)), c)
    | unsnocT (Many (n, xs, ys, F2 (a,b))) = SOME (Many (n, xs, ys, F1 a), b)
    | unsnocT (Many (n, xs, ys, F1 a)) = SOME (Unsnoc (n, xs, ys), a)
    | unsnocT (Pure x) = SOME (Empty, x)
    | unsnocT _ = NONE
  
  fun unconsF (n, xs, ys) =
    case unconsT xs of
        SOME (Node3 (m,a,b,c), xs) => Many (n - m, F3 (a,b,c), ref xs, ys)
      | SOME (Node2 (m,a,b), xs) => Many (n - m, F2 (a,b), ref xs, ys)
      | _ => few ys
  
  fun unsnocF (n, xs, ys) =
    case unsnocT ys of
        SOME (ys, Node3 (m,a,b,c)) => Many (n - m, xs, ref ys, F3 (a,b,c))
      | SOME (ys, Node2 (m,a,b)) => Many (n - m, xs, ref ys, F2 (a,b))
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
    | L of int * 'a seq ref * 'a finger
    | R of int * 'a finger * 'a seq ref
    | M of 'a finger * 'a finger
  
  fun upd (ys, M (xs, zs) :: ss) = upd (Many (size ys, xs, ref ys, zs), ss)
    | upd (xs, _) = xs
  
  fun updT (a, T41 (b,c,d) :: L (m, xs, ys) :: ss) = upd (Many (m, F4 (a,b,c,d), xs, ys), ss)
    | updT (b, T42 (a,c,d) :: L (m, xs, ys) :: ss) = upd (Many (m, F4 (a,b,c,d), xs, ys), ss)
    | updT (c, T43 (a,b,d) :: L (m, xs, ys) :: ss) = upd (Many (m, F4 (a,b,c,d), xs, ys), ss)
    | updT (d, T44 (a,b,c) :: L (m, xs, ys) :: ss) = upd (Many (m, F4 (a,b,c,d), xs, ys), ss)
    | updT (a, T41 (b,c,d) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F4 (a,b,c,d)), ss)
    | updT (b, T42 (a,c,d) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F4 (a,b,c,d)), ss)
    | updT (c, T43 (a,b,d) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F4 (a,b,c,d)), ss)
    | updT (d, T44 (a,b,c) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F4 (a,b,c,d)), ss)
    | updT (a, T31 (b,c) :: L (m, xs, ys) :: ss) = upd (Many (m, F3 (a,b,c), xs, ys), ss)
    | updT (b, T32 (a,c) :: L (m, xs, ys) :: ss) = upd (Many (m, F3 (a,b,c), xs, ys), ss)
    | updT (c, T33 (a,b) :: L (m, xs, ys) :: ss) = upd (Many (m, F3 (a,b,c), xs, ys), ss)
    | updT (a, T31 (b,c) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F3 (a,b,c)), ss)
    | updT (b, T32 (a,c) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F3 (a,b,c)), ss)
    | updT (c, T33 (a,b) :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F3 (a,b,c)), ss)
    | updT (a, T21 b :: L (m, xs, ys) :: ss) = upd (Many (m, F2 (a,b), xs, ys), ss)
    | updT (b, T22 a :: L (m, xs, ys) :: ss) = upd (Many (m, F2 (a,b), xs, ys), ss)
    | updT (a, T21 b :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F2 (a,b)), ss)
    | updT (b, T22 a :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F2 (a,b)), ss)
    | updT (a, T11 :: L (m, xs, ys) :: ss) = upd (Many (m, F1 a, xs, ys), ss)
    | updT (a, T11 :: R (m, xs, ys) :: ss) = upd (Many (m, xs, ys, F1 a), ss)
    | updT (a, T31 (b,c) :: ss) = updT (n3 (a,b,c), ss)
    | updT (b, T32 (a,c) :: ss) = updT (n3 (a,b,c), ss)
    | updT (c, T33 (a,b) :: ss) = updT (n3 (a,b,c), ss)
    | updT (a, T21 b :: ss) = updT (n2 (a,b), ss)
    | updT (b, T22 a :: ss) = updT (n2 (a,b), ss)
    | updT (x, ss) = upd (Pure x, ss)
  
  fun set (x, ss) = updT (Leaf x, ss)
  
  datatype 'a try
    = Tree of 'a tree * 'a step list
    | Fing of 'a finger * 'a step list
    | Memo of int * 'a seq ref * 'a step list
    | Seq of 'a seq * 'a step list
  
  type 'a hole = 'a step list
  
  fun find (n, Memo (m, r, ss) :: ts) =
      if n < m then
        let val xs = force (!r)
        in r := xs; find (n, Seq (xs, ss) :: nil) end
      else
        find (n - m, ts)
    
    | find (n, Seq (Pure x, ss) :: _) = find (n, Tree (x, ss) :: nil)
    | find (n, Seq (Many (m, xs, ys, zs), ss) :: _) =
      find (n, Fing (xs, L (m, ys, zs) :: ss) ::
               Memo (m, ys, M (xs, zs) :: ss) ::
               Fing (zs, R (m, xs, ys) :: ss) :: nil)
    
    | find (n, Fing (F1 a, ss) :: ts) =
      find (n, Tree (a, T11 :: ss) :: ts)
    
    | find (n, Fing (F2 (a,b), ss) :: ts) =
      find (n, Tree (a, T21 b :: ss) ::
               Tree (b, T22 a :: ss) :: ts)
    
    | find (n, Fing (F3 (a,b,c), ss) :: ts) =
      find (n, Tree (a, T31 (b,c) :: ss) ::
               Tree (b, T32 (a,c) :: ss) ::
               Tree (c, T33 (a,b) :: ss) :: ts)
    
    | find (n, Fing (F4 (a,b,c,d), ss) :: ts) =
      find (n, Tree (a, T41 (b,c,d) :: ss) ::
               Tree (b, T42 (a,c,d) :: ss) ::
               Tree (c, T43 (a,b,d) :: ss) ::
               Tree (d, T44 (a,b,c) :: ss) :: ts)
    
    | find (0, Tree (Leaf x, ss) :: _) = SOME (x, ss)
    | find (n, Tree (Leaf _, _) :: ts) = find (n - 1, ts)
    | find (n, Tree (Node2 (m,a,b), ss) :: ts) =
      if n < m then
        find (n, Tree (a, T21 b :: ss) ::
                 Tree (b, T22 a :: ss) :: nil)
      else
        find (n - m, ts)
    
    | find (n, Tree (Node3 (m,a,b,c), ss) :: ts) =
      if n < m then
        find (n, Tree (a, T31 (b,c) :: ss) ::
                 Tree (b, T32 (a,c) :: ss) ::
                 Tree (c, T33 (a,b) :: ss) :: nil)
      else
        find (n - m, ts)
    
    | find _ = NONE
  
  fun get (n, xs) = if n >= 0 then find (n, Seq (xs, nil) :: nil) else NONE
end
