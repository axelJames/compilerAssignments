(*----------STRUCTURES--------------*)

signature NODE = 
sig
	eqtype nod
end

functor Graph (structure node:NODE) = 
 struct
 	
 	type nodeEdge = node.nod * (node.nod list);
 	type graph = nodeEdge list;
 	val empty = [];

 	fun addEdge (n1:node.nod,n2:node.nod) g:graph = case g of
 		[] => g
 		|(f,r)::grest => if f=n1 then (f,([n2]@r))::grest else (f,r)::(addEdge (n1,n2) grest);

 	fun addEdges (n1:node.nod,n2) g:graph = case g of
 		[] => g
 		|(f,r)::grest => if f=n1 then (f,(n2@r))::grest else (f,r)::(addEdges (n1,n2) grest);
 	
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

structure instruction = 
struct
	type inst= string * string list * string list
	fun useSet (x,y,z)= AtomSet.fromList(List.map Atom.atom z) 
	fun defSet (x,y,z)= AtomSet.fromList(List.map Atom.atom y)
end

structure gra = Graph(structure node =
						struct 
							type nod= string
						end)

structure iMap = ListMapFn (struct
							type ord_key = string
							val compare = String.compare
							end);
 

(*---------HELPER FUNCTIONS--------------*)
(*---------------------------------------------------------------------------------------------------------------------------------------*)

fun checkEqual (l1::ls1) (l2::ls2)= if AtomSet.equal(l1,l2) then checkEqual ls1 ls2 else false
	|checkEqual l1 l2= if List.null(l1) andalso List.null(l2) then true else false

fun tostr (x::xs) = (Atom.toString x)::tostr xs
	|tostr [] = [];

fun makeMapfromList li = case li of
	(x,y)::ls => AtomMap.insert(makeMapfromList(ls),Atom.atom(x),y)
	|[] => AtomMap.empty

fun atomSettoSList x= (List.map Atom.toString (AtomSet.listItems(x)))

fun check x y = (x=y)


(*--------------FIND IN AND OUT SET-----------------*)
(*---------------------------------------------------------------------------------------------------------------------------------------*)

fun 


fun findNewOut succ inMap out = case succ of 
	s::xs => findNewOut xs inMap (AtomSet.union(out, getOpt(AtomMap.find(inMap,s),AtomSet.empty)))
	|[] => out

fun iterInOut inMap outMap gr i instMap = case i of
	[] => (inMap,outMap)
	|ins::is => let 
		val nIn= AtomMap.insert
		(inMap,
		ins,
		AtomSet.union
			(instruction.useSet
				(getOpt
					(AtomMap.find(instMap,ins)
					,("",[],[])
					)
				)
			,AtomSet.difference
				(getOpt
					(AtomMap.find(outMap,ins),
					AtomSet.empty
					)
				,instruction.defSet
					(getOpt
						(AtomMap.find(instMap,ins)
						,("",[],[])
						)
					)
				)
			)
			
		)
				in iterInOut nIn (AtomMap.insert(outMap,ins,findNewOut (List.map Atom.atom (gra.suc gr (Atom.toString ins))) nIn AtomSet.empty)) gr is instMap
				 end


fun findInOut inMap outMap gr instMap = let 
	val (newInMap,newOutMap) = (iterInOut inMap outMap gr (List.map Atom.atom (gra.nodes gr)) instMap) in 
	if checkEqual (AtomMap.listItems inMap) (AtomMap.listItems newInMap) andalso checkEqual (AtomMap.listItems outMap) (AtomMap.listItems newOutMap) then
		(inMap,outMap) 
	else findInOut newInMap newOutMap gr instMap
	end


(*--------------FIND GEN SET AND KILL SET OF INSTRUCTIONS----------------*)
(*--------------------------------------------------------------------------------------------------------------------------------*)

fun findGenKill gen kill ins = 
	if List.length(ins)>0 then 
	let val x= List.hd(ins)
	 in findGenKill (AtomSet.union(instruction.useSet(x),AtomSet.difference(gen,instruction.defSet(x)))) (AtomSet.union(kill,instruction.defSet(x))) (List.tl(ins))
	 end
	else (gen,kill)


(*------------FINDING BASIC BLOCKS----------------*)
(*--------------------------------------------------------------------------------------------------------------------------------*)

fun findMembers gr mem l= let val x= gra.suc gr mem in
	if List.length(gra.pred gr mem)<2 orelse mem =l then
		 case x of [y] => ([mem]@(findMembers gr y l))
		 	| _ => [mem]
	else []
	end

fun addLeaders lList li = case li of 
	l::ls => if (List.exists (check l) lList) then (addLeaders lList ls)
			else [l]@(addLeaders lList ls)
	|[] => []

fun findBasic leaderMap lQueue lList gr = case lQueue of 
	l::ls => let val x=findMembers gr l l in 
		findBasic (iMap.insert(leaderMap,l ,x)) (ls@(addLeaders (lList@lQueue) (gra.suc gr (List.last x)))) ([l]@lList) gr end
	|[] => iMap.listItemsi(leaderMap)


(*-----------MAKE GRAPH WITH BASIC BLOCKS AS NODES-------------*)
(*---------------------------------------------------------------------------------------------------------------------------------*)
fun convertGraph gr bGraph leaderMap = case leaderMap of
	(x1,x2)::xs => 
	convertGraph gr (gra.addEdges (x1,(gra.suc gr (List.last(x2)))) (gra.newNode bGraph x1)) xs 
	|[] => bGraph

fun lookupIns insList instMap= case insList of
	x::xs => [AtomMap.lookup(instMap,Atom.atom(x) )]@(lookupIns xs instMap)
	|[] => [] 

fun convertNodes blockMap leaderMap instMap= case leaderMap of 
	(x1,x2)::xs => let val (y1,y2)= findGenKill AtomSet.empty AtomSet.empty (List.rev(lookupIns x2 instMap))
	in convertNodes (AtomMap.insert(blockMap,Atom.atom(x1),(x1,(atomSettoSList(y2)), (atomSettoSList(y1))))) xs instMap
	end
	|[] => blockMap


(*------------MAKE IN AND OUT OF BASIC BLOCKS-----------*)
(*---------------------------------------------------------------------------------------------------------------------------------*)
fun findBlockInOut gr instMap start = let 
	val leaderMap = findBasic iMap.empty [start] [] gr;
	val bGraph = convertGraph gr [] leaderMap;
	val blockMap = convertNodes AtomMap.empty leaderMap instMap;
  in
  	findInOut AtomMap.empty AtomMap.empty bGraph blockMap
  end


(*-------------TEST CASES--------------*)
(*-----------------------------------------------------------------------------------------------------------------------------------*)
(*val bin=findBlockInOut x1 y2 "a"*)

(*val x1 = [("a",["b","c"]),("b",[]),("c",[])]
val u1=(List.map Atom.atom ["l","f"])
val m1=AtomMap.singleton(Atom.atom("a"),("a",["l"],[]:string list))
val y1 = AtomMap.insert(m1,Atom.atom("b"),("b",["m"],["l"]))
val y2 = AtomMap.insert(y1,Atom.atom("c"),("c",["n"],["l"]))
val ab =findInOut AtomMap.empty AtomMap.empty x1 y2
val a = (List.map AtomSet.listItems (AtomMap.listItems(#1 ab))) 
val sa= (List.map tostr a)
val b = (List.map AtomSet.listItems (AtomMap.listItems(#2 ab))) 
val sb= (List.map tostr b)

val xc = [("1",["b"],["a"]),("2",["c"],["c","b"]),("3",["a"],["b"])]
val wqe = findGenKill AtomSet.empty AtomSet.empty (List.rev(xc))
val af = (List.map Atom.toString (AtomSet.listItems(#2 wqe))) *)


val abc = [("1",("1",["a"],[])),("2",("2",["b"],["a"])),("3",("3",["c"],["b","c"])),("4",("4",["a"],["b"])),("5",("5",[],["a"])),("6",("6",[],["c"]))]
val ab1 = makeMapfromList abc
val gs = [("1",["2"]),("2",["3"]),("3",["4"]),("4",["5"]),("5",["2","6"]),("6",[])]
val bin=findBlockInOut gs ab1 "1"
val a = (List.map AtomSet.listItems (AtomMap.listItems(#1 bin))) 
val sa= (List.map tostr a)
val b = (List.map AtomSet.listItems (AtomMap.listItems(#2 bin))) 
val sb= (List.map tostr b)