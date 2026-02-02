(* ::Package:: *)

BeginPackage["ClebschGordanTools`",{"IsotypicDecompositionTools`","TensorTools`"}];


ElementaryClebschGordanTensor
ClebschGordanTensorTrain
ClebschGordanPathsTensorProduct
ClebschGordanPathsExteriorPower
ClebschGordanPathsSymmetricPower
ClebschGordanPathsSchurPower


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


(*https://resources.wolframcloud.com/FunctionRepository/resources/PivotColumns*)
PivotColumns[matrix_?MatrixQ]:=Flatten@Map[Position[#,_?(N@#!=0&),{1},1,Heads->False]&,RowReduce@matrix]


(*helper function that converts the index \[Alpha] to the corresponding spin \[Gamma]*)
indicesToPaths[\[Gamma]_Integer?NonNegative,{\[Lambda]_Integer?NonNegative,\[Alpha]_Integer?NonNegative}]:=Abs[\[Gamma]-\[Lambda]]+\[Alpha]-1


(*helper function that gives the index of the first element in list that is at least the threshold value in thresholds*)
findIndex[list_List?VectorQ,thresholds_List?VectorQ]:=Flatten[Position[list,s_/;#<=s,1,1]&/@thresholds]


(* ::Subsection:: *)
(*Public Functions*)


ElementaryClebschGordanTensor::usage="gives the elementary Clebsch-Gordan tensor coupling \[Lambda]1 and \[Lambda]2 to \[Lambda]3."
ElementaryClebschGordanTensor[\[Lambda]1_Integer?NonNegative,\[Lambda]2_Integer?NonNegative,\[Lambda]3_Integer?NonNegative]:=
 ElementaryClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3]=
  Chop@SparseArray[
   Join@@Table[
    {1+\[Lambda]1+m1,1+\[Lambda]2+m2,1+\[Lambda]3+m1+m2}->N@ClebschGordan[{\[Lambda]1,m1},{\[Lambda]2,m2},{\[Lambda]3,m1+m2}],
    {m1,-\[Lambda]1,\[Lambda]1},
    {m2,Max[-\[Lambda]2,-\[Lambda]3-m1],Min[\[Lambda]2,\[Lambda]3-m1]}
   ],
   {2\[Lambda]1+1,2\[Lambda]2+1,2\[Lambda]3+1}
 ]


ClebschGordanTensorTrain::usage="gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ](*Abs[ListConvolve[{1,-1},\[Gamma]s]]\[VectorLessEqual]Rest[\[Lambda]s]\[VectorLessEqual]ListConvolve[{1,1},\[Gamma]s]*):=
 If[
  Length[\[Lambda]s]==1,(*we should remove calls with length 1 eventually by adjusting code higher up*)
  {1},
  MapThread[ElementaryClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]
 ]


ClebschGordanPathsTensorProduct::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s."
ClebschGordanPathsTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=
 Map[
  Function[indices,FoldList[indicesToPaths,First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],indices}]]],
  Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]
 ]


ClebschGordanPathsExteriorPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold exterior power of \[Lambda]."
SetAttributes[ClebschGordanPathsExteriorPower,Listable]
ClebschGordanPathsExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
 Switch[
  d,
  1,{{\[Lambda]}},
  2,{{\[Lambda],\[Mu]}},
  3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
 ]


ClebschGordanPathsSymmetricPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda]."
SetAttributes[ClebschGordanPathsSymmetricPower,Listable]
ClebschGordanPathsSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
 Switch[
  d,
  1,{{\[Lambda]}},
  2,{{\[Lambda],\[Mu]}},
  3,If[\[Lambda]==\[Mu],{},{{\[Lambda],#+Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}]
 ]


ClebschGordanPathsSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d>=4:=
 Module[
  {
  corePaths,
  coreTensorTrains,
  coreRandomProbes,
  syndromeMatrix,
  coreIndices
  },
  
  corePaths=
   Select[
    ClebschGordanPathsTensorProduct[ConstantArray[\[Lambda],d],\[Mu]],
    EvenQ@#[[2]]&(*symmetry constraint*)
   ];
  
  corePaths=SortBy[corePaths,Boole@FreeQ[Most@#,0]&];(*prioritize lower degree invariants for algebra generation*)
  
  coreTensorTrains=ClebschGordanTensorTrain[ConstantArray[\[Lambda],d]]/@corePaths;
  
  coreRandomProbes=RandomReal[1,{d+d(*oversampling*),2\[Lambda]+1}];
  
  syndromeMatrix=
   Flatten[
    Outer[ContractLeafVectorCoreTensorTrain,coreRandomProbes,coreTensorTrains,1],
    {{1,3},{2}}(*level 3 is the vector of syndromes*)
   ];
  
  coreIndices=PivotColumns@syndromeMatrix;
  
  Select[
   corePaths[[coreIndices]],
   FreeQ[Most@#,0]&(*algebra generation constraint*)
  ]
 ]


(*these expensive functions need to be memoized, since they are evaluated multiple times above. *)
ClebschGordanPathsSchurPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the image of the Young symmetrizer p on \[Lambda]."
ClebschGordanPathsSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]/;First[p]<=3:=
 With[
  {d=Total[p]},
  Switch[
   Length[p],
   1,{{#},{\[Mu]}}&/@ClebschGordanPathsExteriorPower[\[Lambda],d,\[Mu]],
   d,{ConstantArray[{\[Lambda]},d],#}&/@ClebschGordanPathsSymmetricPower[\[Lambda],d,\[Mu]],
   _,
   Module[
    {
     temp,
     coreSpins,corePaths,coreTensorTrains,
     leafPaths,leafTensorTrains,
     leafRandomProbes,coreRandomProbes,
     syndromeMatrix,
     coreIndices,leafIndices
    },
    
    temp=IsotypicComponentsExteriorPower[\[Lambda],p];
    
    If[MemberQ[temp,{0}],Return[{}]];(*algebra generation constraint*)
    
    coreSpins=
     Select[
      Tuples@temp,
      IsotypicComponentTensorProductQ[#,\[Mu]]&
     ];
    
    corePaths=ClebschGordanPathsTensorProduct[#,\[Mu]]&/@coreSpins;
    coreTensorTrains=MapThread[ClebschGordanTensorTrain[#1]/@#2&,{coreSpins,corePaths}];
    
    leafPaths=ClebschGordanPathsExteriorPower[\[Lambda],p,#]&/@coreSpins;
    leafTensorTrains=Map[ClebschGordanTensorTrain[ConstantArray[First@#,Length@#],#]&,leafPaths,{3}];
    
    leafRandomProbes=RandomReal[1,{d+d(*oversampling*),First[p],2\[Lambda]+1}];
    coreRandomProbes=Outer[ContractLeafVectorsAntisymmetrizedTensorTrain,leafRandomProbes,leafTensorTrains,1,3];
    
    (*When First[p]\[LessEqual]3, the subselection below is simple. In general, we would need to take Tuples, and the bookkeeping gets even more complicated.*)
    coreRandomProbes=Flatten[coreRandomProbes,{{1},{2},{3,4}}];
    
    (*somehow we need to sort to the left all paths containing any zero while keeping track of the order. this might be easier in the special case First[p]<=3*)
    
    (*This is unclean but acceptable*)
    syndromeMatrix=
     MapThread[
      Function[
       {coreRandomProbe,coreTensorTrain},
       ContractLeafVectorsCoreTensorTrain[coreRandomProbe,#]&/@coreTensorTrain
      ],
      {#,coreTensorTrains}
     ]&
     /@coreRandomProbes;
    
    syndromeMatrix=Flatten[syndromeMatrix,{{1,4},{2,3}}];
    
    perm=OrderingBy[Flatten[corePaths,1],FreeQ[Most@#,0]&];

    coreIndices=perm[[PivotColumns@syndromeMatrix[[All,perm]]]];
    
    (*temporary solution; this whole function needs to be reviewed and rewritten*)
    coreIndices=Select[coreIndices,FreeQ[Most[Flatten[corePaths,1][[#]]],0]&];
    
    leafIndices=findIndex[Accumulate[Length/@corePaths],coreIndices];
    
    Transpose[{Flatten[leafPaths,{{1},{2},{3,4}}][[leafIndices]],Flatten[corePaths,1][[coreIndices]]}]
   ]
  ]
 ]


End[];


EndPackage[];
