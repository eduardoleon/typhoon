signature STRONGLY_CONNECTED =
sig
  type graph = int list vector
  
  val gabow : graph * int list -> int list list
  val tarjan : graph * int list -> int list list
end

structure StronglyConnected : STRONGLY_CONNECTED =
struct
  structure V = Vector
  structure A = IntArray
  
  type graph = int list vector
  
  fun gabow (graph, roots) =
    let
      datatype step
        = Visit of int list
        | Prune of int
        | Top of int
        | Collect of int * int list
      
      val size = V.length graph
      val index = A.array (size, ~1)
      
      (*  The index of a node k is the number of nodes that have been visited
       *  before the graph traversal reaches k.  We store the index of every
       *  node in the global array.
       *)
      fun run (n, xs, ys, zs, Visit nil :: ss) = run (n, xs, ys, zs, ss)
        | run (n, xs, ys, zs, Visit (k :: ks) :: ss) =
          let in
            case A.sub (index, k) of
                ~1 =>
                let
                  val js = V.sub (graph, k)
                in
                  A.update (index, k, n);
                  run (n + 1, xs, k :: ys, k :: zs, Visit js :: Top k :: Visit ks :: ss)
                end
              | ~2 => run (n, xs, ys,  zs, Visit ks :: ss)
              | c => run (n, xs, ys, zs, Prune c :: Visit ks :: ss)
          end
        
        (*  If j's index is > c, then j is not the earliest visited node in
         *  its strongly connected component.
         *)
        | run (n, xs, ys, zs as j :: js, Prune c :: ss) =
          if A.sub (index, j) > c then
            run (n, xs, ys, js, Prune c :: ss)
          else
            run (n, xs, ys, zs, ss)
        
        (*  If j = k, then k's strongly connected component has been wholly
         *  visited, so we start collecting its nodes.
         *)
        | run (n, xs, ys, zs as j :: js, Top k :: ss) =
          if j = k then
            run (n, xs, ys, js, Collect (k, nil) :: ss)
          else
            run (n, xs, ys, zs, ss)
        
        (*  If j = k, then k's strongly connected component has been wholly
         *  collected, so we resume searching for more strongly connected
         *  components.
         *)
        | run (n, xs, j :: js, zs, Collect (k, ks) :: ss) =
          let in
            A.update (index, j, ~2);
            if j = k then
              run (n, (k :: ks) :: xs, js, zs, ss)
            else
              run (n, xs, js, zs, Collect (k, j :: ks) :: ss)
          end
        
        | run (_, xs, _, _, _) = xs
    in
      run (0, nil, nil, nil, Visit roots :: nil)
    end
  
  fun tarjan (graph, roots) =
    let
      datatype step
        = Visit of int
        | Iter of int * int * int list
        | Bump of int * int * int * int list
        | Collect of int * int list
      
      val size = V.length graph
      val index = A.array (size, ~1)
      
      (*  Let [k] be the earliest visited node that is reachable from k
       *  following a path with at most one backlink.
       *  
       *  We store the index of {k}, where
       *  
       *             | k,      if k is in the control stack,
       *       {k} = | 
       *             | [k],    otherwise.
       *)
      fun run (n, xs, ys, Visit k :: ss) =
          let in
            case A.sub (index, k) of
                ~1 =>
                let
                  val ks = V.sub (graph, k)
                in
                  A.update (index, k, n);
                  run (n + 1, xs, k :: ys, Iter (k, n, ks) :: ss)
                end
              | _ => run (n, xs, ys, ss)
          end
        
        (*  We compute [j] incrementally after visiting every forward
         *  neighbor of j, i.e., every node k with an edge j -> k.
         *)
        | run (n, xs, ys, Iter (j, c, k :: ks) :: ss) =
          run (n, xs, ys, Visit k :: Bump (j, c, k, ks) :: ss)
        
        (*  Whether the edge j -> k is a backlink or not, there exists
         *  a path j -> {k} with at most one backlink.
         *)
        | run (n, xs, ys, Bump (j, c, k, ks) :: ss) =
          let
            val d = A.sub (index, k)
            val c = Int.min (c, d)
          in
            run (n, xs, ys, Iter (j, c, ks) :: ss)
          end
        
        (*  If k's index is c, then k's strongly connected component has
         *  been wholly visited, so we start collecting its nodes.
         *)
        | run (n, xs, ys, Iter (k, c, nil) :: ss) =
          if A.sub (index, k) = c then
            run (n, xs, ys, Collect (k, nil) :: ss)
          else
            let in
              A.update (index, k, c);
              run (n, xs, ys, ss)
            end
        
        (*  If j = k, then k's strongly connected component has been wholly
         *  collected, so we resume searching for more strongly connected
         *  components.
         *)
        | run (n, xs, j :: js, Collect (k, ks) :: ss) =
          let in
            A.update (index, j, size);
            if j = k then
              run (n, (k :: ks) :: xs, js, ss)
            else
              run (n, xs, js, Collect (k, j :: ks) :: ss)
          end
        
        | run (n, xs, _, _) = (n, xs)
      
      fun all (_, xs, nil) = xs
        | all (n, xs, y :: ys) =
          let val (n, xs) = run (n, xs, nil, Visit y :: nil)
          in all (n, xs, ys) end
    in
      all (0, nil, roots)
    end
end
