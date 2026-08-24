signature CRIT_BIT_TREE =
sig
  type 'a tree
  type 'a leaf
  type 'a node
  
  datatype 'a focus = Leaf of 'a * 'a leaf | Node of 'a node
  
  val pure : 'a -> 'a tree
  val empty : 'a leaf
  
  val root : 'a tree -> 'a focus
  val left : 'a node -> 'a focus
  val right : 'a node -> 'a focus
  
  val index : 'a node -> int
  val above : 'a node -> 'a leaf
  val below : 'a node -> 'a node
  
  val insleft : int * 'a tree * 'a leaf -> 'a leaf
  val insright : int * 'a tree * 'a leaf -> 'a leaf
  val update : 'a tree * 'a leaf -> 'a tree
  val delete : 'a leaf -> 'a tree option
  
  type 'a iter_asc
  type 'a iter_desc
  
  val toAsc : 'a tree option -> 'a iter_asc
  val nextAsc : 'a iter_asc -> 'a option
  
  val toDesc : 'a tree option -> 'a iter_desc
  val nextDesc : 'a iter_desc -> 'a option
end

structure CritBitTree :> CRIT_BIT_TREE =
struct
  datatype 'a tree = Pure of 'a | Many of int * 'a tree * 'a tree
  datatype 'a move = L of int * 'a tree | R of int * 'a tree
  
  type 'a leaf = 'a move list
  type 'a node = int * 'a tree * 'a tree * 'a move list
  
  val pure = Pure
  val empty = nil
  val index = #1
  val above = #4
  fun below (n, a, b, _) = (n, a, b, nil)
  
  fun find (m, a, sss as L (n, b) :: ss) = if m < n then find (m, Many (n, a, b), ss) else (a, sss)
    | find (m, b, sss as R (n, a) :: ss) = if m < n then find (m, Many (n, a, b), ss) else (b, sss)
    | find (_, xs, nil) = (xs, nil)
  
  fun insleft (n, xs, ss) =
    let val (xs, ss) = find (n, xs, ss)
    in L (n, xs) :: ss end
  
  fun insright (n, xs, ss) =
    let val (xs, ss) = find (n, xs, ss)
    in R (n, xs) :: ss end
  
  fun update (a, L (n, b) :: ss) = update (Many (n, a, b), ss)
    | update (b, R (n, a) :: ss) = update (Many (n, a, b), ss)
    | update (xs, nil) = xs
  
  fun delete (L (_, xs) :: ss) = SOME (update (xs, ss))
    | delete (R (_, xs) :: ss) = SOME (update (xs, ss))
    | delete nil = NONE
  
  datatype 'a focus = Leaf of 'a * 'a leaf | Node of 'a node
  
  fun focus (Pure x, ss) = Leaf (x, ss)
    | focus (Many (n, a, b), ss) = Node (n, a, b, ss)
                                        
  fun root xs = focus (xs, nil)
  fun left (n, a, b, ss) = focus (a, L (n, b) :: ss)
  fun right (n, a, b, ss) = focus (b, R (n, a) :: ss)
  
  type 'a iter_asc = 'a tree list ref
  type 'a iter_desc = 'a tree list ref
  
  fun loop (_, nil) = NONE
    | loop (r, Pure x :: ss) = SOME x before r := ss
    | loop (r, Many (_,a,b) :: ss) = loop (r, a :: b :: ss)
  
  fun toAsc NONE = ref nil
    | toAsc (SOME xs) = ref (xs :: nil)
  
  fun nextAsc r = loop (r, !r)
  
  fun loop (_, nil) = NONE
    | loop (r, Pure x :: ss) = SOME x before r := ss
    | loop (r, Many (_,a,b) :: ss) = loop (r, b :: a :: ss)
  
  fun toDesc NONE = ref nil
    | toDesc (SOME xs) = ref (xs :: nil)
  
  fun nextDesc r = loop (r, !r)
end
