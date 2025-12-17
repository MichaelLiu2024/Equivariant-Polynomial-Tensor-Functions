(* ::Package:: *)

(*use one space for indents: i think this matches the notebook formatting*)


BeginPackage["CombinatoricsTools`"];


StrictCompositions
WeakCompositions
StandardYoungTableau
ConjugateTableau
ConjugatePartition
SchurS
SemiStandardYoungTableaux


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


pathToSSYT[pathIn_List]:=
  With[
    {{m,nrows}=Dimensions@pathIn},
    {path=Prepend[pathIn,ConstantArray[0,nrows]]},
    
    Table[
      Join@@Table[
        ConstantArray[If[e-1==0,None,e-1],path[[e+1,r]]-path[[e,r]]],
        {e,m}
      ],
      {r,nrows}
    ]
  ];


(* ::Subsubsection:: *)
(*Public Functions*)


StrictCompositions::usage="gives a list of all strict integer compositions of D into n parts"
SetAttributes[StrictCompositions,Listable]
StrictCompositions[D_Integer?NonNegative,n_Integer?Positive]:=Join@@Permutations/@IntegerPartitions[D,{n}]


WeakCompositions::usage="gives a list of all weak integer compositions of D into n parts"
SetAttributes[WeakCompositions,Listable]
WeakCompositions[D_Integer?NonNegative,n_Integer?Positive]:=Join@@Permutations/@IntegerPartitions[D,{n},Range[0,D]]


StandardYoungTableau::usage="gives the standard Young tableau of shape p filled in English reading order"
StandardYoungTableau[p_List?VectorQ]:=TakeList[Range@Total@p,p]


ConjugateTableau::usage="gives the Young tableau conjugate to t"
ConjugateTableau[t_List]:=Flatten[t,{2}]


(*https://resources.wolframcloud.com/FunctionRepository/resources/ConjugatePartition/*)
ConjugatePartition::usage="gives the integer partition conjugate to p"
ConjugatePartition[p_List?VectorQ]:=Total@UnitStep@Outer[Plus,p,-Range@First@p]


(*https://resources.wolframcloud.com/FunctionRepository/resources/SchurS*)
SchurS::usage="gives the Schur polynomial corresponding to the integer partition p in the variables vars."
SchurS[p_List?VectorQ,vars_List?VectorQ]:=
  With[
    {n=Length@vars,id=Range@First@p},
    {elist=Table[SymmetricPolynomial[k,vars],{k,n}]},
    
    Det@Outer[
      With[{r=Plus@##},Which[r==0,1,0<r<=n,elist[[r]],n<r,0]]&,
      ConjugatePartition@p-id,
      id
    ]
  ]


(*https://github.com/PerAlexandersson/Mathematica-packages*)
SemiStandardYoungTableaux::usage="gives a list of all semistandard Young tableaux of shape p with largest entry n"
SemiStandardYoungTableaux[p_List?VectorQ,n_Integer?Positive]:=Join@@SemiStandardYoungTableaux[p]/@IntegerPartitions[Tr@p,{n}]
SemiStandardYoungTableaux[p_List?VectorQ][w_List?VectorQ]:=SemiStandardYoungTableaux[p,w]
SemiStandardYoungTableaux[p_List?VectorQ,w_List?VectorQ]:=
  With[
    {
      mu=ConstantArray[0,First@p],
      mid=IntegerPartitions[#,{First@p},Range[0,Length@p]]&/@Most@Accumulate@w,
      cp=ConjugatePartition@p
    },
    {
      partitionLevels=Join[{{mu}},mid,{{cp}}]
    },
    {
      g=Graph@Join@@Table[
        Join@@Outer[
          If[Min[#2-#1]>=0&&Min[#1[[;;-2]]-#2[[2;;]]]>=0,DirectedEdge[{#1,lvl-1},{#2,lvl}],Nothing]&,
          partitionLevels[[lvl-1]],
          partitionLevels[[lvl]],
          1
        ],
        {lvl,2,Length[partitionLevels]}
      ]
    },
    {
      ssytPaths=If[
        Or[!MemberQ[VertexList[g],{mu,1}],!MemberQ[VertexList[g],{cp,Length[w]+1}]],
        {},
        FindPath[g,{mu,1},{cp,Length[w]+1},Infinity,All]
      ];
    },
    
    Map[ConjugateTableau[pathToSSYT[First/@#]]&,ssytPaths]
  ];


End[];


EndPackage[];
