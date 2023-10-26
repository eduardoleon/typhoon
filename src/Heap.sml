signature ORDERED =
sig
  type elem
  
  val <= : elem * elem -> bool
end

signature BASIC_HEAP =
sig
  type elem
  type heap
  
  val empty : heap
  val cons : elem * heap -> heap
  val uncons : heap -> (elem * heap) option
  val unsnoc : heap -> (heap * elem) option
end

signature HEAP =
sig
  type elem
  type heap
  
  val pure : elem -> heap
  val head : heap -> elem
  val tail : heap -> heap option
  val link : heap * heap -> heap
end

functor SplayHeap (E : ORDERED) :> BASIC_HEAP where type elem = E.elem =
struct
  open E
  
  datatype heap = Empty | Node of heap * elem * heap
  
  val empty = Empty
  
  fun l3 (a,x,b,y,c) = Node (a, x, Node (b,y,c))
  fun r3 (a,x,b,y,c) = Node (Node (a,x,b), y, c)
  fun l4 (a,x,b,y,c,z,d) = Node (a, x, l3 (b,y,c,z,d))
  fun r4 (a,x,b,y,c,z,d) = Node (r3 (a,x,b,y,c), z, d)
  
  datatype step = L of elem * heap | R of heap * elem
  
  fun merge (Node (a,x,b), L (y,c) :: L (z,d) :: ss) = merge (l4 (a,x,b,y,c,z,d), ss)
    | merge (Node (c,z,d), R (b,y) :: R (a,x) :: ss) = merge (r4 (a,x,b,y,c,z,d), ss)
    | merge (Node (a,x,b), L (y,c) :: ss) = merge (l3 (a,x,b,y,c), ss)
    | merge (Node (b,y,c), R (a,x) :: ss) = merge (r3 (a,x,b,y,c), ss)
    | merge (xs, _) = xs
  
  fun split (p, Empty, ss) = merge (Node (Empty, p, Empty), ss)
    | split (p, Node (a,x,b), ss) =
      if p <= x then split (p, a, L (x,b) :: ss)
                else split (p, b, R (a,x) :: ss)
  
  fun cons (x, xs) = split (x, xs, nil)
  
  fun merge (a, (x,b) :: (y,c) :: ss) = merge (l3 (a,x,b,y,c), ss)
    | merge (a, (x,b) :: nil) = Node (a,x,b)
    | merge (xs, nil) = xs
  
  fun split (Node (a,x,b), ss) = split (a, (x,b) :: ss)
    | split (Empty, (x, xs) :: ss) = SOME (x, merge (xs, ss))
    | split (Empty, nil) = NONE
  
  fun uncons xs = split (xs, nil)
  
  fun merge (c, (b,y) :: (a,x) :: ss) = merge (r3 (a,x,b,y,c), ss)
    | merge (b, (a,x) :: nil) = Node (a,x,b)
    | merge (xs, nil) = xs
  
  fun split (Node (a,x,b), ss) = split (b, (a,x) :: ss)
    | split (Empty, (xs, x) :: ss) = SOME (merge (xs, ss), x)
    | split (Empty, nil) = NONE
  
  fun unsnoc xs = split (xs, nil)
end

functor PairingHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  datatype heap = ::: of elem * heap list
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = x <= y
  
  fun link (ys as x ::: xss, xs as y ::: yss) =
    if x <= y then x ::: xs :: xss
              else y ::: ys :: yss
  
  fun hard (x :: y :: xs, ys) = hard (xs, link (x, y) :: ys)
    | hard (x :: nil, xs) = SOME (foldl link x xs)
    | hard (nil, x :: xs) = SOME (foldl link x xs)
    | hard (nil, nil) = NONE
  
  fun tail (_ ::: xs) = hard (xs, nil)
end

functor LazyPairingHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  datatype pair
    = Pure of heap
    | Many of heap * heap * pair ref option
  
  and heap = Heap of elem * heap option * pair ref option
  
  fun pure x = Heap (x, NONE, NONE)
  fun head (Heap (x, _, _)) = x
  fun comp (Heap (x, _, _), Heap (y, _, _)) = x <= y
  fun soft (Heap (x, NONE, xss), ys) = Heap (x, SOME ys, xss)
    | soft (Heap (x, SOME xs, xss), ys) = Heap (x, NONE, SOME (ref (Many (xs, ys, xss))))
  
  fun link (xs, ys) = if comp (xs, ys) then soft (xs, ys) else soft (ys, xs)
  
  datatype step = Link of heap * heap | Memo of pair ref
  
  fun build (Pure x, ss) = (x, ss)
    | build (Many (x, y, NONE), ss) = (link (x, y), ss)
    | build (Many (x, y, SOME r), ss) = build (!r, Memo r :: Link (x, y) :: ss)
  
  fun break (xs, nil) = xs
    | break (xs, Memo r :: ss) = (r := Pure xs; break (xs, ss))
    | break (xs, Link ys :: ss) = break (link (xs, link ys), ss)
  
  fun hard r = break (build (!r, Memo r :: nil))
  fun tail (Heap (_, NONE, NONE)) = NONE
    | tail (Heap (_, NONE, SOME ys)) = SOME (hard ys)
    | tail (Heap (_, SOME xs, NONE)) = SOME xs
    | tail (Heap (_, SOME xs, SOME ys)) = SOME (link (xs, hard ys))
end
