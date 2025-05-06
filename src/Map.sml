signature SET =
sig
  type key
  type set
  type rest
  
  val empty : set
  val get : key * set -> bool * rest
  val set : bool * rest -> set
  
  val toAsc : set -> key list
  val toDesc : set -> key list
end

signature MAP =
sig
  type key
  type 'a elem = key * 'a
  type 'a map
  type 'a rest
  
  val empty : 'a map
  val get : key * 'a map -> 'a option * 'a rest
  val set : 'a option * 'a rest -> 'a map
  
  val toAsc : 'a map -> 'a elem list
  val toDesc : 'a map -> 'a elem list
end
