structure RedBlackTree :> SEARCH_TREE =
struct
  datatype 'a tree
    = Empty
    | Red of 'a tree * 'a * 'a tree
    | Black of 'a tree * 'a * 'a tree
  
  val empty = Empty
  fun pure x = Red (Empty, x, Empty)
  
  fun l2 ((a,x,b),y,c) = (a, x, Red (b,y,c))
  fun r2 (a,x,(b,y,c)) = (Red (a,x,b), y, c)
  
  fun u3 (a,x,b,y,c) = Black (a, x, Red (b,y,c))
  fun l3 (a,x,b,y,c) = Red (Black a, x, Black (b,y,c))
  fun r3 (a,x,b,y,c) = Red (Black (a,x,b), y, Black c)
  fun m3 (a,x,(b,y,c),z,d) = Red (Black (a,x,b), y, Black (c,z,d))
  
  datatype 'a step = L of 'a * 'a tree | R of 'a tree * 'a | T
  
  (*  Rebuild without rebalancing.  *)
  fun upd (Red xs, T :: ss) = upd (Black xs, ss)
    | upd (a, L (x,b) :: ss) = upd (Red (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Red (a,x,b), ss)
    | upd (xs, _) = xs
  
  (*  Rebuild after inserting, pushing children out of the focused node.  *)
  fun ins (Red a, L (x,b) :: L (y,c) :: T :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (Red b, R (a,x) :: L (y,c) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red b, L (y,c) :: R (a,x) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red c, R (b,y) :: R (a,x) :: T :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (Red xs, nil) = Black xs
    | ins xs = upd xs
  
  (*  Rebuild after deleting, pulling children into the focused node.  *)
  fun del (a, T :: L (x, Red (b,y,c)) :: ss) = del (a, T :: L (x,b) :: L (y,c) :: ss)
    | del (c, T :: R (Red (a,x,b), y) :: ss) = del (c, T :: R (b,y) :: R (a,x) :: ss)
    | del (a, T :: L (x, Black (Red b,y,c)) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (c, T :: R (Black (a,x,Red b), y) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (a, T :: L (x, Black b) :: ss) = del (Black (r2 (a,x,b)), ss)
    | del (b, T :: R (Black a, x) :: ss) = del (Black (l2 (a,x,b)), ss)
    | del xs = upd xs
  
  (*    *)
  fun old (Red b, L (y,c) :: R (a,x) :: T :: ss) = old (m3 (a,x,b,y,c), ss)
    | old (Red a, L (x,b) :: ss) = old (Red (l2 (a,x,b)), ss)
    | old (Red b, R (a,x) :: ss) = old (Red (r2 (a,x,b)), ss)
    | old (xs, _) = xs
  
  fun new (b, L (y,c) :: R (a,x) :: T :: ss) = new (u3 (a,x,b,y,c), ss)
    | new (a, L (x,b) :: ss) = old (Red (a,x,b), ss)
    | new (b, R (a,x) :: ss) = old (Red (a,x,b), ss)
    | new (xs, _) = xs
  
  fun cut (Black (a,x,b), Black (c,y,d), ss) = cut (b, c, L (y,d) :: R (a,x) :: T :: ss)
    | cut (a, Red (b,x,c), ss) = cut (a, b, L (x,c) :: ss)
    | cut (Red (a,x,b), c, ss) = cut (b, c, R (a,x) :: ss)
    | cut (xs, _, ss) = new (xs, ss)
  
  type 'a leaf = 'a step list
  type 'a hole = 'a tree * 'a tree * 'a step list
  
  fun splay ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Red (a, x, b), ss)
  fun insert (x, ss) = ins (pure x, ss)
  fun delete (a, b, ss) =
    case cut (a, b, nil) of
        xs as Red _ => upd (xs, ss)
      | xs => del (xs, ss)
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Red (a, x, b), ss) = Node (x, (a, b, ss))
    | focus (Black (a, x, b), ss) = Node (x, (a, b, T :: ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x, b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a, x) :: ss)
  fun prune (a, b, _) = (a, b, T :: nil)
  
  datatype 'a step = ^ of 'a tree * 'a
  
  fun rot (a^x, b^y) = Red (a,x,b) ^ y
  
  fun one (us, Red a ^ x :: vs) = one (Black a ^ x :: us, vs)
    | one (u :: us, v :: vs) = List.revAppend (us, rot (v,u) :: vs)
    | one xs = List.revAppend xs
  
  fun all (x :: xs, ss) = all (xs, one (Empty ^ x :: nil, ss))
    | all (nil, ss) = ss
  
  fun upd (b, a^x :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, nil) = xs
  
  fun fromAsc xs = upd (Empty, all (xs, nil))
  
  datatype 'a step = ^ of 'a * 'a tree
  
  fun rot (x^a, y^b) = x ^ Red (a,y,b)
  
  fun one (us, x ^ Red a :: vs) = one (x ^ Black a :: us, vs)
    | one (u :: us, v :: vs) = List.revAppend (us, rot (u,v) :: vs)
    | one xs = List.revAppend xs
  
  fun all (x :: xs, ss) = all (xs, one (x ^ Empty :: nil, ss))
    | all (nil, ss) = ss
  
  fun upd (a, x^b :: ss) = upd (Black (a,x,b), ss)
    | upd (xs, nil) = xs
  
  fun fromDesc xs = upd (Empty, all (xs, nil))
  
  datatype 'a step = One of 'a | Many of 'a tree
  
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
