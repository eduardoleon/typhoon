signature PREFIX_TREE =
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
  
  val toAsc : 'a tree option -> 'a list
  val toDesc : 'a tree option -> 'a list
end
