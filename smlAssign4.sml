signature NODE = 
sig
	eqtype nod
end

fun comp (x,y) = if (x = y) then EQUAL else (if (x>y) then GREATER else LESS)

functor Graph (structure node:NODE) = 
 struct
 	
 	type nodeEdge = node.nod * (node.nod list);
 	type graph = nodeEdge list;
 	val empty = [];

 	fun addEdge (n1:node.nod,n2:node.nod) g:graph = case g of
 		[] => g
 		|(f,r)::grest => if f=n1 then (f,([n2]@r))::grest else (f,r)::(addEdge (n1,n2) grest);
 	
 	fun newNode (g:nodeEdge list) (n1:node.nod) = [(n1,[])]@g

 	fun nodes g = case g of 
 		[] => []
 		|(f,r)::grest => f::(nodes grest)

 	fun suc g n1 = case g of 
 		[] => []
 		|(f,r)::grest => if (f=n1) then r else suc grest n1

 	fun check x y = (x=y)

 	fun pred g n1 = case g of 
 		[] => []
 		|(f,r)::grest => if (List.exists (check n1) r) then [f]@(pred grest n1)
 							else pred grest n1
 end 


structure intNode:NODE = 
struct
	type nod=int
end

fun check x y = (x=y)

structure gra = Graph(structure node= intNode)

structure iMap = ListMapFn (struct
							type ord_key = intNode.nod
							val compare = comp
							end);
 
fun findMembers gr mem l= let val x= gra.suc gr mem in
	if List.length(gra.pred gr mem)<2 orelse mem =l then
		 case x of [y] => ([mem]@(findMembers gr y l))
		 	| _ => [mem]
	else []
	end

(*fun findMembers gr mem l= let val x= gra.suc gr mem in
							 case x of 
							 	[y] => (if List.length(gra.pred gr mem)<2 orelse mem = l then ([mem]@(findMembers gr y l)) else [])
								| _ => (if List.length(gra.pred gr mem)<2 orelse mem =l then [mem] else [])
						end
*)
fun addLeaders lList li = case li of 
	l::ls => if (List.exists (check l) lList) then (addLeaders lList ls)
			else [l]@(addLeaders lList ls)
	|[] => []

fun findBasic leaderMap lQueue lList gr = case lQueue of 
	l::ls => let val x=findMembers gr l l in findBasic (iMap.insert(leaderMap,l ,x)) (ls@(addLeaders (lList@lQueue) (gra.suc gr (List.last x)))) ([l]@lList) gr end
	|[] => leaderMap


val x = gra.empty
val x = gra.newNode x 1
val x = gra.newNode x 2
val x = gra.newNode x 3
val x = gra.addEdge (1,2) x
val x = gra.addEdge (1,3) x
(*val basicBlocks = findBasic iMap.empty [1] [] [(1,[2,3]),(2,[]),(3,[])]*)
val x1 = [(1,[2,6]),(2,[3]),(3,[4]),(4,[]),(5,[4]),(6,[5])]
val x2 = [(9,[10,11]),(1,[2]),(2,[3]),(3,[4]),(4,[5,2]),(5,[6,7]),(6,[8]),(8,[]),(7,[9]),(10,[]),(11,[])]
val y=findBasic iMap.empty [1] [] x2
val z=iMap.listItemsi y