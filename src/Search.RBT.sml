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
  
  datatype 'a step = L of 'a * 'a tree | R of 'a tree * 'a | T | W
  
  fun upd (Red xs, T :: ss) = upd (Black xs, ss)
    | upd (a, L (x,b) :: ss) = upd (Red (a,x,b), ss)
    | upd (b, R (a,x) :: ss) = upd (Red (a,x,b), ss)
    | upd (xs, _) = xs
  
  fun ins (Red a, L (x,b) :: L (y,c) :: T :: ss) = ins (l3 (a,x,b,y,c), ss)
    | ins (Red b, R (a,x) :: L (y,c) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red b, L (y,c) :: R (a,x) :: T :: ss) = ins (m3 (a,x,b,y,c), ss)
    | ins (Red c, R (b,y) :: R (a,x) :: T :: ss) = ins (r3 (a,x,b,y,c), ss)
    | ins (Red xs, nil) = Black xs
    | ins xs = upd xs
  
  fun del (a, T :: L (x, Red (b,y,c)) :: ss) = del (a, T :: L (x,b) :: L (y,c) :: ss)
    | del (c, T :: R (Red (a,x,b), y) :: ss) = del (c, T :: R (b,y) :: R (a,x) :: ss)
    | del (a, T :: L (x, Black (Red b,y,c)) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (c, T :: R (Black (a,x,Red b), y) :: ss) = upd (m3 (a,x,b,y,c), ss)
    | del (a, T :: L (x, Black b) :: ss) = del (Black (r2 (a,x,b)), ss)
    | del (b, T :: R (Black a, x) :: ss) = del (Black (l2 (a,x,b)), ss)
    | del xs = upd xs
  
  fun old (Red b, W :: L (y,c) :: R (a,x) :: ss) = old (m3 (a,x,b,y,c), ss)
    | old (Red a, W :: L (x,b) :: ss) = old (Red (l2 (a,x,b)), ss)
    | old (Red b, W :: R (a,x) :: ss) = old (Red (r2 (a,x,b)), ss)
    | old xs = upd xs
  
  fun new (b, W :: L (y,c) :: R (a,x) :: ss) = new (u3 (a,x,b,y,c), ss)
    | new (a, W :: L (x,b) :: ss) = old (Red (a,x,b), ss)
    | new (b, W :: R (a,x) :: ss) = old (Red (a,x,b), ss)
    | new xs = del xs
  
  fun cut (Black (a,x,b), Black (c,y,d), ss) = cut (b, c, W :: L (y,d) :: R (a,x) :: ss)
    | cut (a, Red (b,x,c), ss) = cut (a, b, W :: L (x,c) :: ss)
    | cut (Red (a,x,b), c, ss) = cut (b, c, W :: R (a,x) :: ss)
    | cut (xs, _, ss) = new (xs, ss)
  
  type 'a leaf = 'a step list
  type 'a hole = 'a tree * 'a tree * 'a step list
  
  fun splay ss = upd (Empty, ss)
  fun update (x, (a, b, ss)) = upd (Red (a, x, b), ss)
  fun insert (x, ss) = ins (pure x, ss)
  val delete = cut
  
  datatype 'a focus = Leaf of 'a leaf | Node of 'a * 'a hole
  
  fun focus (Empty, ss) = Leaf ss
    | focus (Red (a, x, b), ss) = Node (x, (a, b, ss))
    | focus (Black (a, x, b), ss) = Node (x, (a, b, T :: ss))
  
  fun root xs = focus (xs, nil)
  fun left (x, (a, b, ss)) = focus (a, L (x, b) :: ss)
  fun right (x, (a, b, ss)) = focus (b, R (a, x) :: ss)
  fun prune (a, b, _) = (a, b, T :: nil)
  
  datatype 'a step = ^ of 'a tree * 'a
  
  fun upd (a ^ x, b) = Black (a,x,b)
  fun rot (a ^ x, b ^ y) = Red (a,x,b) ^ y
  fun cut (us, vs) = foldl op:: us vs
  fun ins (Red a ^ x :: us, vs) = ins (us, Black a ^ x :: vs)
    | ins (u :: us, v :: vs) = cut (us, rot (u, v) :: vs)
    | ins xs = cut xs
  
  fun cons (x, ss) = ins (ss, Empty ^ x :: nil)
  fun fromAsc xs = foldl upd Empty (foldl cons nil xs)
  
  datatype 'a step = ^ of 'a * 'a tree
  
  fun upd (x ^ b, a) = Black (a,x,b)
  fun rot (x ^ a, y ^ b) = x ^ Red (a,y,b)
  fun cut (us, vs) = foldl op:: vs us
  fun ins (us, x ^ Red a :: vs) = ins (x ^ Black a :: us, vs)
    | ins (u :: us, v :: vs) = cut (rot (u, v) :: us, vs)
    | ins xs = cut xs
  
  fun cons (x, ss) = ins (x ^ Empty :: nil, ss)
  fun fromDesc xs = foldl upd Empty (foldl cons nil xs)
  
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
