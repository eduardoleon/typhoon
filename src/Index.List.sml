signature INDEXABLE_LIST =
sig
  type 'a list
  type 'a hole
  
  val empty : 'a list
  val cons : 'a * 'a list -> 'a list
  val uncons : 'a list -> ('a * 'a list) option
  
  val drop : int * 'a list -> 'a list
  val get : int * 'a list -> ('a * 'a hole) option
  val set : 'a * 'a hole -> 'a list
end
