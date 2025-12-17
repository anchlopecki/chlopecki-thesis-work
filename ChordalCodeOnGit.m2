restart

loadPackage "NautyGraphs"
loadPackage "Chordal"
loadPackage "Depth"
loadPackage "AlgebraicSplines"

-- user inputs v and d
v = 5 -- number of vertices
-- e = 4 -- number of edges, ranges from v to (v*(v-1))//2

d = 2 -- minor size

-- creates ring and matrix corresponding to inputted graph
createStructures = method();
createStructures(Graph) := g -> (
    -- create ring
    variabs = new MutableList from {};
    for edge in edges(g) do (
        edgeAsList = toList(edge);
	if (edgeAsList#0 < edgeAsList#1) then (
	    variabs = append(variabs, concatenate("x_",toString(edgeAsList#0+1),toString(edgeAsList#1+1))); -- relabel edges with +1 value so that does not get dropped in poly. ring
	    );
	if (edgeAsList#1 < edgeAsList#0) then (
	    variabs = append(variabs, concatenate("x_",toString(edgeAsList#1+1),toString(edgeAsList#0+1)))
	    );
	variabs = toList(variabs);
	variabs = apply(variabs, f -> value(f)); -- huh????? thank you Adam
	);
    R = QQ[variabs];
    
    N = mutableMatrix(R, v, v);
    
    -- modify diagonal entires of N
    tempEntryDiag = 0;
    for i from 0 to v-1 do (
	neighList = toList(neighbors(g, i));
        for j from 0 to #neighList-1 do (
	    if (i<neighList#j) then (
		tempEntryDiag = tempEntryDiag + value(concatenate("x_",toString(i+1),toString(neighList#j+1)));
		);
	    if (i>neighList#j) then (
		tempEntryDiag = tempEntryDiag + value(concatenate("x_",toString(neighList#j+1),toString(i+1)));
		);
	    );
	N_(i,i) = tempEntryDiag;
	tempEntryDiag = 0;
	);

    -- modify non-diagonal entries of N
    for i from 0 to v-1 do (
	for j from 0 to v-1 do (
	    if (i != j) then (
		-- checks whether an edge exists between two vertices
		if (member(set({i,j}),edges(g))) then (
		    if (i<j) then (
			N_(i,j) = -value(concatenate("x_",toString(i+1),toString(j+1)));
			);
		    if (i>j) then (
			N_(i,j) = -value(concatenate("x_",toString(j+1),toString(i+1)));
			);
		    );
		);
	    );
	);
    (R,N)
    )

-- creates ring and matrix corresponding to inputted graph with PEO
createStructuresPEO = method();
createStructuresPEO(Graph) := g -> (
    -- create ring with PEO ordering (CHECK WORK)
    variabs = new MutableList from {};
    perfElimOrder = createsPerfElimOrder(g);
    edgesAsList = new MutableList from edges(g);
    
    for i from 0 to v-1 do (
	neighsOfi = apply(toList(neighbors(g, perfElimOrder#i)), x -> value(toString(x)));
	for j from 0 to v-1 do (
	    if i != j then (
		if (member(perfElimOrder#j, neighsOfi) and member(set({perfElimOrder#i, perfElimOrder#j}), toList(edgesAsList))) then (
		    variabs = append(variabs, concatenate("x_",toString(perfElimOrder#i+1),toString(perfElimOrder#j+1))); -- relabel edges with +1 value so that does not get dropped in poly. ring
		    posOfEdge = position(toList(edgesAsList), x -> x == set({perfElimOrder#i, perfElimOrder#j}));
		    edgesAsList = take(toList(edgesAsList), posOfEdge) | drop(toList(edgesAsList), posOfEdge+1);
		    );
		variabs = toList(variabs);
		variabs = apply(variabs, f -> value(f)); -- huh????? thank you Adam
	        );
	    );
        );
    R = QQ[variabs];
    
    N = mutableMatrix(R, v, v);
    
    -- modify diagonal entires of N
    tempEntryDiag = 0;
    for i from 0 to v-1 do (
	neighsOfi = apply(toList(neighbors(g, perfElimOrder#i)), x -> value(toString(x)));
	for j from 0 to v-1 do (
	    if i != j then (
		if member(perfElimOrder#j, neighsOfi) then (
		    if i < j then (
			tempEntryDiag = tempEntryDiag + value(concatenate("x_",toString(perfElimOrder#i+1),toString(perfElimOrder#j+1)));
			);
		    if j < i then (
			tempEntryDiag = tempEntryDiag + value(concatenate("x_",toString(perfElimOrder#j+1),toString(perfElimOrder#i+1)));
		        );
		    );
	        );
	    );
	N_(perfElimOrder#i, perfElimOrder#i) = tempEntryDiag;
	tempEntryDiag = 0;
        );

    -- modify non-diagonal entries of N
    for i from 0 to v-1 do (
	neighsOfi = apply(toList(neighbors(g, perfElimOrder#i)), x -> value(toString(x)));
	for j from 0 to v-1 do (
	    if i != j then (
		if member(perfElimOrder#j, neighsOfi) then (
		    if i < j then (
			N_(perfElimOrder#i, perfElimOrder#j) = -value(concatenate("x_",toString(perfElimOrder#i+1),toString(perfElimOrder#j+1)));
			);
		    if j < i then (
		        N_(perfElimOrder#i, perfElimOrder#j) = -value(concatenate("x_",toString(perfElimOrder#j+1),toString(perfElimOrder#i+1)));
		        );
		    );
		);
	    );
	);
 
    (R,N)
    )

-- returns true or false, depending on if the ideal of d-minors corresponding to graph g is Hilbertian or not, respectively
checkHilbertian = method();
checkHilbertian(PolynomialRing, MutableMatrix) := (R, N) -> ( 
    J = minors(d, matrix(N));

    S = R/J;

    hilbPoly = hilbertPolynomial(S, Projective => false);
    hilbSeries = hilbertSeries(J);

    ourOutput = true;

    -- MODIFY 100 !!!
    for i from 0 to 100 do (
	if (hilbPoly(i) != hilbertFunction({i},S)) then (
	    -- print "Not Hilbertian!";
	    ourOutput = false;
	    );
	);
    ourOutput
    )

-- returns true or false, depending on if diagonal elements of matrix AXA^T form a regular sequence or not, respectively
checkRegularSequence = method();
checkRegularSequence(PolynomialRing, MutableMatrix) := (R, N) -> (
    numRowsOfN = numRows(N);
    diagEntries = new MutableList from {};
    
    for i from 0 to numRowsOfN-2 do ( -- MODIFIED FROM -1 to -2 (do not take bottom corner entry)
	diagEntries = append(diagEntries, N_(i,i));
	);
    
    isRegularSequence(toList(diagEntries))
    -- CODE WHICH CHECKS ALL POSSIBLE ORDERINGS OF DIAGONAL ENTRIES
    -- potOrders = permutations(toList(diagEntries));
    -- outputList = new MutableList from {};
    -- for orderOfSeq in potOrders do (
	-- if (isMember(toString(isRegularSequence(toList(orderOfSeq))),toList(outputList)) != true) then (outputList = append(outputList,toString(isRegularSequence(toList(orderOfSeq)))));
	-- );
    -- print length(toList(outputList));
    )

-- returns postulation number
checkPostulationNumber = method();
checkPostulationNumber(PolynomialRing, MutableMatrix) := (R,N) -> (
    J = minors(d, matrix(N));
    S = R^1/J;   
    postulationNumber(S)
    )

-- returns true if ideal of 2-minors is generated by a GB
checkGB = method();
checkGB(PolynomialRing, MutableMatrix) := (R,N) -> (
    J = minors(d, matrix(N));
    
    -- mingens(J) == gens(gb(J))
    
    -- check definition of GB
    idealAsList = J_*;
    initTermList = new MutableList from {};
    for i from 0 to #idealAsList-1 do (
	if leadCoefficient(leadTerm(idealAsList#i)) < 0 then (
	    initTermList = append(initTermList, -1*leadTerm(idealAsList#i));
	    );
	if leadCoefficient(leadTerm(idealAsList#i)) >= 0 then (
	    initTermList = append(initTermList, leadTerm(idealAsList#i));
	    );
	);
    initTermList = unique(toList(initTermList));
    set((leadTerm(J))_*) == set(initTermList)
    )

-- returns perfect elimination ordering of graph in a list
createsPerfElimOrder = method();
createsPerfElimOrder(Graph) := (actualGraph) -> (
    sigma = new MutableList from {toList(0..v-1)};
    outputSeq = new MutableList from {};
    L = toList(sigma);
    O = toList(outputSeq);

    while L != {} do (
	-- find and remove a vertex v from the first set in sigma (i.e. L)
	currVertex = L#0#0;
	L = {take(L#0, -(#(L#0)-1))} | drop(L,1);
	
	-- if the first set in L is now empty, remove it from L
	if L#0 == {} then (
	    L = drop(L,1);
	    );
    
	-- add v to the end of the output sequence
	O = append(O, currVertex);
	
	-- modification to while loop
	neighL = toList(neighbors(actualGraph, currVertex));
	lenOfL = #L;
	for i from 0 to lenOfL-1 do (
	    S = L#i;
	    T = new MutableList from {};
	    lenOfS = #S;
	    for j from 0 to lenOfS-1 do (
		if member(S#j, neighL) then (
		    T = append(T, S#j);
		    );
		);
	    -- print peek T;
	    -- insert T
	    if toList(T) != {} then (
		L = take(L, i) | {toList(T)} | drop(L,i);
		-- print L;
		-- throw away redundencies from S that are in T
		ammendedS = new MutableList from {};
		for k from 0 to lenOfS-1 do (
		    if (member(S#k, toList(T)) == false) then (
			ammendedS = append(ammendedS, S#k);
			);
		    );
		if toList(ammendedS) != {} then (
		    L = take(L, i+1) | {toList(ammendedS)} | drop(L, i+2);
		    );
		if toList(ammendedS) == {} then (
		    L = take(L, i+1) | drop(L, i+2);
		    );
		);
	    );
	);   
    reverse(O)
    )

G = generateGraphs(v, v, (v*(v-1))//2, OnlyConnected => true);

listOfGraphsToTest = new MutableList from {} -- graphs to test

for graph in G do (
    actualGraph = stringToGraph(graph);
    if (vertexConnectivity(actualGraph) != 1) then (listOfGraphsToTest = append(listOfGraphsToTest, graph));
    )

for graph in listOfGraphsToTest do (
    --actualGraph = stringToGraph(graph);
    --(R, N) = createStructures(actualGraph);
    -- print R;
    -- print N;
    
    -- ELIMINATION TREE ???
    -- print actualGraph;
    -- print elimTree(chordalGraph(actualGraph));
    -- print "------------------";
    
    -- REGULAR SEQUENCE CHECK
    -- if (checkRegularSequence(R,N) != true) then (print actualGraph);
    -- if (checkRegularSequence(R,N) != true) then (print isChordal(actualGraph));
    -- if (checkRegularSequence(actualGraph,R,N) == false) then (print actualGraph);
    -- if (checkRegularSequence(actualGraph,R,N) == false) then (print actualGraph);
    
    -- CHORDAL CHECK
    -- if isChordal(actualGraph) then (print checkHilbertian(R,N));
    -- PRINT ELIMINATION TREE
    -- print elimTree(chordalGraph(actualGraph));
    
    -- NOT CHORDAL CHECK
    -- if (isChordal(actualGraph) != true) then (print checkHilbertian(R,N));
    -- if (isChordal(actualGraph) != true) then (print graph);

    -- POSTULATION NUMBER
    -- print actualGraph;
    -- print checkPostulationNumber(R,N);

    -- PRINTS OUT PEO
    -- if (isChordal(actualGraph) == true) then (print actualGraph);
    -- if (isChordal(actualGraph) == true) then (print createsPerfElimOrder(actualGraph));

    -- CREATES (R,N) USING PEO
    -- actualGraph = stringToGraph(graph);
    -- if (isChordal(actualGraph) == true) then (
	-- print(actualGraph);
	-- print createsPerfElimOrder(actualGraph);
	-- (R,N) = createStructuresPEO(actualGraph);
	-- print N;
	-- );

    -- CHECKS GB
    -- actualGraph = stringToGraph(graph);
    -- if (isChordal(actualGraph) == true) then (
        -- print(actualGraph);
	-- print createsPerfElimOrder(actualGraph);
	-- (R,N) = createStructuresPEO(actualGraph);
        -- print N;
	-- print checkGB(R,N);
	-- );
    )

-- code to check any graph
A = matrix{{0,1,0,0,1},{1,0,0,0,1},{0,0,0,1,1},{0,0,1,0,1},{1,1,1,1,0}};
print A;
g = graph(A);
print g;
print createsPerfElimOrder(g);
(R,N) = createStructuresPEO(g);
print N;
print gens(R);

print "Done!";

-- COUNTEREXAMPLE FOUND FOR NOT CHORDAL BUT HILBERTIAN
-- print isChordal(stringToGraph("E]~w"));
-- print stringToGraph("E]~w");
-- #edges(stringToGraph("E]~w"))
-- (R,N) = createStructures(stringToGraph("E]~w"));
-- print checkHilbertian(R,N);
