

datatype Symbol = Term of string| NonTerm of string | Eps of string;
type Left = string;
type Right = Symbol list;
type Prod = Left * Right;
type Productions = Prod list;
type Start = string;
type Grammar =   Productions * Start;
type SymbolList = Symbol list;

structure sSet = ListSetFn (struct
							type ord_key = string
							val compare = String.compare
							end);

structure sMap = ListMapFn (struct
							type ord_key = string
							val compare = String.compare
							end);

(*---------------------------------------------------------------------------------------------------------------------*)

fun symToString sym = case sym of
	Term sym => sym
	|NonTerm sym => sym
	|Eps sym => "e$"

fun getTerms(right,termlist) = case right of
	x::xs =>(case x of
		Term x => [x]@getTerms(xs,termlist)
		|NonTerm x => getTerms(xs,termlist)
		|Eps x => getTerms(xs,termlist))
	|[] => termlist

fun getTermSymbol(prods:Productions,termlist) = case prods of
	((left,right):: productions) => getTerms(right,[])@getTermSymbol(productions,termlist)
	| [] => termlist@[]

fun getNontermSymbol(prods:Productions,nontermlist) = case prods of
	((left,right):: productions) => [left]@getNontermSymbol(productions,nontermlist)
	| [] => nontermlist@[]

(*fun getSymbolSet (productions:Productions , s:Start) = getSymbol (productions)*)
(*---------------------------------------------------------------------------------------------------------------------*)

val pprod:Productions = [("E",[NonTerm "T",NonTerm "E1"]),
("E1",[Term "+",NonTerm "T",NonTerm "E1"]),("T",[NonTerm "F",NonTerm "T1"]),
("T1",[Term "*",NonTerm "F",NonTerm "T1"]),("F",[Term "(",NonTerm "E",Term ")"]),
("F",[Term "id"]),("E1",[Eps "e$"]),("T1",[Eps "e$"])]
val nontermList = getNontermSymbol(pprod,[]) ;
val termList = getTermSymbol(pprod,[])

val nontermSet = sSet.addList(sSet.empty,nontermList);
val termSet = sSet.addList(sSet.empty,termList);

val tlist = sSet.listItems(termSet)
val ntlist = sSet.listItems(nontermSet)

(*---------------------------------------------------------------------------------------------------------------------*)


fun addProds(X,right,mmap)= case right of
	x::xs => (case getOpt(sMap.find(mmap,x),sSet.empty) of
			z => if sSet.member(z,"e$") then  
					sMap.unionWith (fn (w,y) => sSet.union(w,y)) 
					(sMap.unionWith (fn (w,y) => sSet.union(w,y)) 
					(mmap,sMap.singleton(X,sSet.delete(z,"e$"))),addProds(X,xs,mmap)) 
				else sMap.unionWith (fn (w,y) => sSet.union(w,y)) (mmap,sMap.singleton(X,z)))
				
	|[] => sMap.unionWith (fn (w,y) => sSet.union(w,y)) (mmap,sMap.singleton(X,sSet.singleton("e$")))

fun iterProds(X, prods, mmap)=case prods of
	(Y , right)::prod =>  if X=Y then 
		iterProds(X,prod,addProds (X,(List.map symToString right),mmap))
		else iterProds(X,prod,mmap)
	|[] => mmap

fun iterSymbols(ntlist, prods:Productions, mmap)= case ntlist of
	x::xs => iterSymbols(xs,prods,iterProds(x,prods,mmap))
	|[]=> mmap 

fun preFirst(tlist,mmap) = case tlist of
	t::tl => preFirst(tl,sMap.insert(mmap,(t),sSet.singleton(t)))
	|[] => mmap

fun calcFirst(ntlist, prods:Productions , mmap) = let 
	val x = iterSymbols(ntlist, prods,mmap)
	in if(List.map sSet.listItems (sMap.listItems(mmap))=(List.map sSet.listItems (sMap.listItems x))) then mmap
		else calcFirst(ntlist, prods, x)
	end

val mmap = calcFirst(ntlist,pprod,preFirst(tlist,sMap.singleton("e$",sSet.singleton("e$"))));


(*-----------------------------------------------------------------------------------------------------------------*)

fun firstBeta(nontermSet,X,mmap,firstSet) = case X of
	x::xs => (case getOpt(sMap.find(mmap,x),sSet.empty) of
				z => if sSet.member(z,"e$") andalso sSet.member(nontermSet,x) then
					sSet.union(sSet.delete(z,"e$"),firstBeta(nontermSet,xs,mmap,firstSet))
					else
					sSet.union(z,firstSet))
	|[] => sSet.union(sSet.singleton("e$"),firstSet);

fun iterRight(nontermSet,right,Y,mmap,fmap) = case right of
	x::xs => if sSet.member(nontermSet,x) then 
				let val z=firstBeta(nontermSet,xs,mmap,sSet.empty)
				in if sSet.member(z,"e$") then iterRight(nontermSet,xs,Y,mmap,
					sMap.unionWith (fn (w,y) => sSet.union(w,y)) 
					(fmap,sMap.singleton(x,sSet.delete(sSet.union(z,getOpt(sMap.find(fmap,Y),sSet.empty)),"e$"))))

				else iterRight(nontermSet,xs,Y,mmap,sMap.unionWith (fn (w,y) => sSet.union(w,y)) (fmap,sMap.singleton(x,z)))
				end
			else iterRight(nontermSet,xs,Y,mmap,fmap)
	| [] => fmap;

fun iterProductions(nontermSet, prods,mmap, fmap)=case prods of
	(Y , right)::prod => iterProductions(nontermSet,prod,mmap,iterRight(nontermSet,(List.map symToString right),Y,mmap,fmap))
	|[] => fmap;

fun calcFollow(nontermSet, prods:Productions ,mmap, fmap) = let 
	val x = iterProductions(nontermSet, prods,mmap,fmap)
	in if(List.map sSet.listItems (sMap.listItems(fmap))=(List.map sSet.listItems (sMap.listItems x))) then fmap
		else calcFollow(nontermSet, prods,mmap, iterProductions(nontermSet, prods,mmap,x))
	end;

val fmap= calcFollow(nontermSet,pprod,mmap,sMap.singleton("E",sSet.singleton("$")));

(*-----------------------------------------------------------------------------------------------------------------*)

val inputSymbol = tlist@["$"];
val lltable = Array2.array(List.length(ntlist),List.length(inputSymbol),[]:SymbolList);

fun findPos(nlist,item,pos)= case nlist of
	x::xs => if x=item then pos else findPos(xs,item,pos+1)
	|[] => ~1

fun modifyTable(lltable,r,c,right)= case (Array2.update(lltable,r,c,right)) of
	() => lltable


fun add(lltable,followList,left,right) = case followList of
	x::xs => add(modifyTable(lltable,findPos(ntlist,left,0),findPos(inputSymbol,x,0),right),xs,left,right)
	|[] => lltable


fun updateTable(lltable,left,fir,right) = case fir of
	x::xs=>if (x="e$") then if sSet.member(getOpt(sMap.find(fmap,left),sSet.empty),"$") then
							updateTable( add( modifyTable(lltable,findPos(ntlist,left,0),findPos(inputSymbol,"$",0),right), sSet.listItems(getOpt(sMap.find(fmap,left),sSet.empty)),left,right),left,xs,right) 
						else 
							updateTable(add(lltable,sSet.listItems(getOpt(sMap.find(fmap,left),sSet.empty)),left,right)   ,left,xs,right)
	else updateTable(modifyTable(lltable,findPos(ntlist,left,0),findPos(inputSymbol,x,0),right),left,xs,right)
	| []=>lltable


fun makeLLtable(lltable,prods:Productions) = case prods of
	(left,right)::xs => makeLLtable( updateTable( lltable,left, sSet.listItems( firstBeta( nontermSet,(List.map symToString right),mmap,sSet.empty)),right),xs)
	|[]=>lltable 

val lltab = makeLLtable(lltable,pprod);


(*--------------------------------------------------------------------------------------------------------------------*)

print("first");
val fi = List.map sSet.listItems (sMap.listItems(mmap));
val fo = List.map sSet.listItems (sMap.listItems(fmap));
Array2.sub(lltab,1,1);
Array2.row(lltab,0);
