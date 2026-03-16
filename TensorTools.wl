(* ::Package:: *)

BeginPackage["TensorTools`",{"CombinatoricsTools`","BooleanTools`"}];


EvaluateTensorTrain
EvaluateAntisymmetrizedTensorTrain
EvaluateSymmetrizedTensorTrain
EvaluateAntisymmetrizedTensorTree
EvaluateYoungSymmetrizedTensorTree


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


ContractVectors[vector1_,{vector2_,tensor_}]:=Dot[vector2,Dot[vector1,tensor]]


AntisymmetrizationData[d_?PositiveIntegerQ] :=
 AntisymmetrizationData[d] =
  With[
   {permutations = Select[Permutations @ Range @ d, #[[1]] < #[[2]] &]},
   
   {2/Factorial[d], Signature /@ permutations, permutations}
  ]


(* ::Subsubsection:: *)
(*Public Functions*)


EvaluateTensorTrain::usage="evaluates the tensorTrain at the vectors."


EvaluateTensorTrain[{1},vectors_List]:=First@vectors


EvaluateTensorTrain[tensorTrain_List,vectors_List]:=Fold[ContractVectors,First@vectors,Transpose[{vectors[[2;;1+Length@tensorTrain]],tensorTrain}]]


EvaluateAntisymmetrizedTensorTrain::usage="contracts the antisymmetrized tensorTrain with the vectors."


EvaluateAntisymmetrizedTensorTrain[{1},vectors_List]:=First@vectors


(*assumes the first tensor factor is Antisymmetric[{1,2}]*)
EvaluateAntisymmetrizedTensorTrain[tensorTrain_List,vectors_List] :=
  With[
   {data = AntisymmetrizationData[1 + Length @ tensorTrain]},
   
   First@data*
    Total @ MapThread[
      #1 EvaluateTensorTrain[tensorTrain, vectors[[#2]]] &,
      Rest@data
    ]
  ]


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."


EvaluateSymmetrizedTensorTrain[{1},vector_List?VectorQ]:=vector


EvaluateSymmetrizedTensorTrain[tensorTrain_List,vector_List?VectorQ]:=Fold[Dot[vector,Dot[#1,#2]]&,vector,tensorTrain]


EvaluateAntisymmetrizedTensorTree[tensorTrees_Association,vectors_List]:=
 With[
  {interiorVectors=Map[EvaluateAntisymmetrizedTensorTrain[#,vectors]&,tensorTrees[["leafObjects"]],{2}]},
  
  MapThread[EvaluateTensorTrain,{tensorTrees[["interiorTensorTrains"]],interiorVectors}]
 ]


SymmetrizedMonomialCP[variables_List,powers_List]:=SymmetrizedMonomialCP[powers][variables]
SymmetrizedMonomialCP[powers_List] :=
  SymmetrizedMonomialCP[powers]=
   With[
    {ds=ReplacePart[powers,1->0], d=Total@powers, n=Length@powers},
    {\[Zeta]s=Exp[(2\[Pi]*I)/(ds+1)]},
    {grid=Sequence@@(\[Zeta]s^Range[0,ds])},
    {const=1/(Times@@(ds+1)*Multinomial@@powers)},
    
    Function[
     variables,
     {
      const,
      Flatten[Outer[Times[##]^(1/d)*{##} . variables &, grid], n - 1]
     }
    ]
   ]


PartiallySymmetrizedMonomialCP[variables_List,SSYT_List]:=
 Transpose@MapThread[
  SymmetrizedMonomialCP,
  {(variables[[#]]&)/@First/@SSYT,Last/@SSYT}
 ]


EvaluateYoungSymmetrizedTensorTree[tensorTrees_Association,{{}},variables_List]:=ConstantArray[{{{1}}},Length@variables]


EvaluateYoungSymmetrizedTensorTree[tensorTrees_Association,SSYTs_List,variables_List]:=
  With[
   {
    (*variables; SSYTs; {globalCoefficient, localVariables}*)
    CPData=Outer[PartiallySymmetrizedMonomialCP,variables,SSYTs,1]
   },
   
   (*
   Level 1: variables
   Level 2: SSYTs
   Level 3: tensorTrees
   Object:  vector
   *)
   Map[
    Times@@First@#*
     Total[
      Outer[
       EvaluateAntisymmetrizedTensorTree[tensorTrees,{##}]&,
       Sequence@@Last@#,
       1
      ],
      Length@Last@#
     ]&,
    CPData,
    {2}
   ]
  ]


End[];


EndPackage[];
