restart

loadPackage "NautyGraphs"
loadPackage "Chordal"
loadPackage "Depth"
loadPackage "AlgebraicSplines"
loadPackage "TestIdeals"
loadPackage "GeometricDecomposability"

-- user inputs v and d
v = 5 -- number of vertices
-- e = 4 -- number of edges, ranges from v to (v*(v-1))//2

d = 2 -- minor size

-- creates ring and matrix corresponding to inputted graph with Revlex Order
createStructuresGRevlex = method();
createStructuresGRevlex(Graph) := g -> (
    local variabs;
    local edgeAsList;
    local R;
    local N;
    local tempEntryDiag;
    local neighList;
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
    R = QQ[variabs, MonomialOrder => GRevLex];
    
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

-- creates ring and matrix corresponding to inputted graph with Lex Order
createStructuresLex = method();
createStructuresLex(Graph) := g -> (
    local variabs;
    local edgeAsList;
    local R;
    local N;
    local tempEntryDiag;
    local neighList;
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
    R = QQ[variabs, MonomialOrder => Lex];
    
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

-- creates ring and matrix corresponding to inputted graph with Revlex Order and modified variable order
createStructuresGRevlexMod = method();
createStructuresGRevlexMod(Graph) := g -> (
    local variabs;
    local neighborList;
    local numNeighbors;
    local toAdd;
    -- create ring
    variabs = new MutableList from {};
    for vertex in reverse(0..v-1) do (
	neighborList = toList(neighbors(g, vertex));
	numNeighbors = #neighborList;
	for neighbor in reverse(0..numNeighbors-1) do (
	    if vertex > neighborList#neighbor then (
		toAdd = concatenate("x_",toString(neighborList#neighbor+1),toString(vertex+1));
		if member(toAdd, toList(variabs)) == false then (
		    variabs = prepend(toAdd, variabs);
		    );
		);
	    if neighborList#neighbor > vertex then (
		toAdd = concatenate("x_",toString(vertex+1),toString(neighborList#neighbor+1));
		if member(toAdd, toList(variabs)) == false then (
		    variabs = prepend(toAdd, variabs);
		    );
		);
	    );
	);
    variabs = toList(variabs);
    variabs = apply(variabs, f -> value(f)); -- huh????? thank you Adam
    R = QQ[variabs, MonomialOrder => GRevLex];

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

-- creates ring and matrix corresponding to inputted graph with Lex Order and modified variable order
createStructuresLexMod = method();
createStructuresLexMod(Graph) := g -> (
    local variabs;
    local neighborList;
    local numNeighbors;
    local toAdd;
    -- create ring
    variabs = new MutableList from {};
    for vertex in reverse(0..v-1) do (
	neighborList = toList(neighbors(g, vertex));
	numNeighbors = #neighborList;
	for neighbor in reverse(0..numNeighbors-1) do (
	    if vertex > neighborList#neighbor then (
		toAdd = concatenate("x_",toString(neighborList#neighbor+1),toString(vertex+1));
		if member(toAdd, toList(variabs)) == false then (
		    variabs = prepend(toAdd, variabs);
		    );
		);
	    if neighborList#neighbor > vertex then (
		toAdd = concatenate("x_",toString(vertex+1),toString(neighborList#neighbor+1));
		if member(toAdd, toList(variabs)) == false then (
		    variabs = prepend(toAdd, variabs);
		    );
		);
	    );
	);
    variabs = toList(variabs);
    variabs = apply(variabs, f -> value(f)); -- huh????? thank you Adam
    R = QQ[variabs, MonomialOrder => Lex];

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

-- examples
A = matrix{{0,1,0,1,0},{1,0,1,0,1},{0,1,0,1,0},{1,0,1,0,0},{0,1,0,1,0}}; -- adjacency matrix
g = graph(A);
print g;
-- GRevLex
(R,N) = createStructuresGRevlex(g);
(options R).MonomialOrder
gens R
J = minors(d,matrix(N));M
gens J
mingens J
leadTerm(J)
numgens(leadTerm(J))
-- Lex
(S,M) = createStructuresLex(g);
(options S).MonomialOrder
gens S
I = minors(d,matrix(M));
leadTerm(I)
numgens(leadTerm(I))
-- Modified Variable Order and GRevLex
(T,L) = createStructuresGRevlexMod(g);
(options T).MonomialOrder
gens T
K = minors(d,matrix(L));
leadTerm(K)
numgens(leadTerm(K))
-- Modified Term Order and Lex
(U,O) = createStructuresLexMod(g);
(options U).MonomialOrder
gens U
A = minors(d,matrix(O));
leadTerm(A)
numgens(leadTerm(A))
