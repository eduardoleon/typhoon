structure RedBlackTree :> SEARCH_TREE =
struct
  datatype 'a tree
    = Empty
    | Red of 'a tree * 'a * 'a tree
    | Black of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Red (Empty, x, Empty)
  
  fun l2 ((a,x,b),y,c) = Red (a, x, Red (b,y,c))
  fun r2 (a,x,(b,y,c)) = Red (Red (a,x,b), y, c)
  
  fun l3 (a,x,b,y,c) = Red (Black a, x, Black (b,y,c))
  fun r3 (a,x,b,y,c) = Red (Black (a,x,b), y, Black c)
  fun m3 (a,x,(b,y,c),z,d) = Red (Black (a,x,b), y, Black (c,z,d))
  
  fun u3 (Red a,x,b,y,c) = l3 (a,x,b,y,c)
    | u3 (a,x,b,y,Red c) = r3 (a,x,b,y,c)
    | u3 (a,x,b,y,c) = Black (a, x, Red (b,y,c))
  
  (*  By default, nodes are red, i.e., they do not contribute to the tree's
   *  black height.  However, we can turn them black when needed.
   *)
  datatype 'a move = L of 'a * 'a tree | R of 'a tree * 'a | B
  
  fun upd (a, L (x,b) :: B :: ss) = upd (Black (a,x,b), ss)
    | upd (b, R (a,x) :: B :: ss) = upd (Black (a,x,b), ss)
    | upd (a, L (x,b) :: ss) = upd (Red (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Red (a,x,b), ss)
    | upd (xs, _) = xs
  
  (*  Rotate outward after an insertion to restore the red-red invariant.  *)
  fun ins (Red a, L (x,b) :: L (y,c) :: B :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (Red b, R (a,x) :: L (y,c) :: B :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red b, L (y,c) :: R (a,x) :: B :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red c, R (b,y) :: R (a,x) :: B :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (Red xs, nil) = Black xs
    | ins xs = upd xs
  
  (*  Rotate inward after a deletion to restore the black height invariant.  *)
  fun del (Red xs, B :: ss) = del (Black xs, ss)
    | del (Red xs, ss) = upd (Black xs, ss)
    | del (a, L (x, Red (b,y,c)) :: ss) = del (a, L (x,b) :: L (y,c) :: ss)
    | del (c, R (Red (a,x,b), y) :: ss) = del (c, R (b,y) :: R (a,x) :: ss)
    | del (a, L (x, Black (Red b,y,c)) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (c, R (Black (a,x,Red b), y) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (a, L (x, Black b) :: ss) = del (r2 (a,x,b), ss)
    | del (b, R (Black a, x) :: ss) = del (l2 (a,x,b), ss)
    | del (xs, _) = xs
  
  (*  Restore the subtree originally rooted at the deleted element.  *)
  fun sew (Red b, L (y,c) :: R (a,x) :: B :: ss) = sew (m3 (a,x,b,y,c), ss)
    | sew (Red a, L (x,b) :: ss) = sew (l2 (a,x,b), ss)
    | sew (Red b, R (a,x) :: ss) = sew (r2 (a,x,b), ss)
    | sew (b, L (y,c) :: R (a,x) :: B :: ss) = sew (u3 (a,x,b,y,c), ss)
    | sew (a, L (x,b) :: ss) = sew (Red (a,x,b), ss)
    | sew (b, R (a,x) :: ss) = sew (Red (a,x,b), ss)
    | sew (xs, _) = xs
  
  (*  Rotate the node to be deleted downward until it has no children.  *)
  fun cut (Black (a,x,b), Black (c,y,d), ss) = cut (b, c, L (y,d) :: R (a,x) :: B :: ss)
    | cut (a, Red (b,x,c), ss) = cut (a, b, L (x,c) :: ss)
    | cut (Red (a,x,b), c, ss) = cut (b, c, R (a,x) :: ss)
    | cut (xs, _, ss) = sew (xs, ss)
  
  type 'a leaf = 'a move list
  type 'a hole = 'a tree * 'a tree * 'a move list
  
  fun splay ss = upd (Empty, ss)
  fun insert (x, ss) = ins (pure x, ss)
  
  fun update (x, (a, b, B :: ss)) = upd (Black (a,x,b), ss)
    | update (x, (a, b, ss)) = upd (Red (a,x,b), ss)
  
  fun delete (a, b, B :: ss) = del (cut (a, b, nil), ss)
    | delete (a, b, ss) = upd (cut (a, b, nil), ss)
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Red (a,x,b), ss) = Node (x, (a, b, ss))
    | focus (Black (a,x,b), ss) = Node (x, (a, b, B :: ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x,b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a,x) :: ss)
  fun prune (a, b, _) = (a, b, B :: nil)
  
  (*  To build a red-black tree from a sorted list, we work with zippers focused on
   *  the rightmost leaf, satisfying the additional invariant that the entire path
   *  to this leaf consists of black nodes only.
   *  
   *  Inserting a single element is a two-phase operation:
   *  
   *  -  Ascend the tree to restore the aforementioned invariant.
   *  -  Descend the tree to refocus on the rightmost leaf.
   *)
  
  (*  Second phase  *)
  fun cut (Red (a,x,b), ss) = cut (b, R (a,x) :: ss)
    | cut (_, ss) = ss
  
  (*  First phase  *)
  fun ins (b, R (Red a, x) :: ss) = ins (Red (Black a, x, b), ss)
    | ins (Red b, R (a,x) :: ss) = cut (r2 (a,x,b), ss)
    | ins xs = cut xs
  
  fun upd (b, R (a,x) :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromAsc xs = all (xs, nil)
  
  (*  To build a tree from a descendingly sorted list, we use the same algorithm
   *  as in the ascending case, except we now work with zippers focused on the
   *  leftmost, rather than rightmost leaf.
   *)
  
  (*  Second phase  *)
  fun cut (Red (a,x,b), ss) = cut (a, L (x,b) :: ss)
    | cut (_, ss) = ss
  
  (*  First phase  *)
  fun ins (a, L (x, Red b) :: ss) = ins (Red (a, x, Black b), ss)
    | ins (Red a, L (x,b) :: ss) = cut (l2 (a,x,b), ss)
    | ins xs = cut xs
  
  fun upd (a, L (x,b) :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun all (x :: xs, ss) = all (xs, ins (pure x, ss))
    | all (nil, ss) = upd (Empty, ss)
  
  fun fromDesc xs = all (xs, nil)
  
  (*  To build a list from a tree, we work with chunks consisting of one or several
   *  elements.  A single element can be directly shifted to the final list, whereas
   *  a chunk of many elements is further split into subchunks.
   *)
  datatype 'a chunk = One of 'a | Many of 'a tree
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Red (a, x, b)) :: ss) = loop (xs, Many b :: One x :: Many a :: ss)
    | loop (xs, Many (Black (a, x, b)) :: ss) = loop (xs, Many b :: One x :: Many a :: ss)
  
  fun toAsc xs = loop (nil, Many xs :: nil)
  
  fun loop (xs, nil) = xs
    | loop (xs, One x :: ss) = loop (x :: xs, ss)
    | loop (xs, Many Empty :: ss) = loop (xs, ss)
    | loop (xs, Many (Red (a, x, b)) :: ss) = loop (xs, Many a :: One x :: Many b :: ss)
    | loop (xs, Many (Black (a, x, b)) :: ss) = loop (xs, Many a :: One x :: Many b :: ss)
  
  fun toDesc xs = loop (nil, Many xs :: nil)
end
