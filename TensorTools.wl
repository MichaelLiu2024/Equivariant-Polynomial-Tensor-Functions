(* ::Package:: *)

BeginPackage["TensorTools`",{"CombinatoricsTools`"}];


ContractLeafVectorsCoreTensor
ContractLeafSSYTCoreTensor
ContractLeafVectorsCoreTensorTrain
ContractLeafVectorsAntisymmetrizedTensorTrain
ContractLeafTensorsCoreTensorTrain
ContractLeafVectorCoreTensorTrain
ContractCoreTensorTrain
EvaluateYoungSymmetrizedTensorTree
AntisymmetrizeRows
SymmetrizeColumns
YoungSymmetrize


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


ContractVectors[leafVector1_?VectorQ,{leafVector2_?VectorQ,coreTensor_?ArrayQ}]:=Dot[leafVector2,Dot[leafVector1,coreTensor]]


ContractTensors[leafTensor1_?ArrayQ,{leafTensor2_?ArrayQ,coreTensor_?ArrayQ}]:=
 With[
  {r1=TensorRank@leafTensor1,r2=TensorRank@leafTensor2},
  
  TensorContract[
   TensorProduct[
    leafTensor1,
    TensorContract[
     TensorProduct[leafTensor2,coreTensor],
     {{r2,r2+2}}
    ]
   ],
   {{r1,r1+r2}}
  ]
 ]


(* ::Subsubsection:: *)
(*Public Functions*)


ContractLeafVectorsCoreTensorTrain::usage="contracts the coreTensorTrain with the leafVectors."
ContractLeafVectorsCoreTensorTrain[leafVectors_List,coreTensorTrain_List]:=
 If[
  coreTensorTrain==={1},
  First@leafVectors,
  Chop@Fold[ContractVectors,First@leafVectors,Transpose[{leafVectors[[2;;1+Length@coreTensorTrain]],coreTensorTrain}]]
 ]


ContractLeafVectorsAntisymmetrizedTensorTrain::usage="contracts the antisymmetrized coreTensorTrain with the leafVectors."
(*assumes the first tensor factor is Antisymmetric[{1,2}]*)
ContractLeafVectorsAntisymmetrizedTensorTrain[leafVectors_List,coreTensorTrain_List]:=
 Switch[
  Length[coreTensorTrain],
  1,ContractLeafVectorsCoreTensorTrain[leafVectors,coreTensorTrain],
  2,
   (ContractLeafVectorsCoreTensorTrain[leafVectors,coreTensorTrain]
   -ContractLeafVectorsCoreTensorTrain[leafVectors[[{3,2,1}]],coreTensorTrain]
   -ContractLeafVectorsCoreTensorTrain[leafVectors[[{1,3,2}]],coreTensorTrain])/3
 ]


(*ContractLeafVectorSymmetrizedTensorTrain*)
ContractLeafVectorCoreTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."
ContractLeafVectorCoreTensorTrain[leafVector_List?VectorQ,coreTensorTrain_List]:=
 If[
  coreTensorTrain==={1},
  leafVector,
  Chop@Fold[Dot[leafVector,Dot[#1,#2]]&,leafVector,coreTensorTrain]
 ]


(*stuff to discard eventually, since we no longer form full tensors*)


(*this will be removed eventually*)
ContractLeafSSYTCoreTensorTrain[leafSSYT_List,coreTensorTrain_List]:=
With[
{coreDimensions=First@*Rest@*Dimensions/@coreTensorTrain},
{leafVectors=MapThread[With[{\[Lambda]=(#1-1)/2},Table[Subscript[Global`x, \[Lambda],m,#2],{m,-\[Lambda],\[Lambda]}]]&,{coreDimensions,Flatten[leafSSYT]}]},
ContractLeafVectorsCoreTensorTrain[leafVectors,coreTensorTrain]
]


(*This is really a generalized Tucker format...*)
EvaluateYoungSymmetrizedTensorTree[leafVectors_List,leafTensors_List,coreTensorTrain_List]:=ContractLeafVectorsCoreTensorTrain[ContractLeafVectorsCoreTensor[leafVectors]/@leafTensors,coreTensorTrain]


ContractLeafTensorsCoreTensorTrain::usage="contracts the coreTensorTrain with the leafTensors."
ContractLeafTensorsCoreTensorTrain[leafTensors_List,coreTensorTrain_List]:=
 If[
  Length[leafTensors]==1,
  Chop@Dot[First@leafTensors,First@coreTensorTrain],
  Chop@Fold[ContractTensors,First[leafTensors],Transpose[{Rest[leafTensors],coreTensorTrain}]]
 ]


ContractLeafVectorsCoreTensor::usage="contracts the leftmost modes of coreTensor with the leafVectors."
ContractLeafVectorsCoreTensor[leafVectors_List][coreTensor_?ArrayQ]:=ContractLeafVectorsCoreTensor[leafVectors,coreTensor]
ContractLeafVectorsCoreTensor[leafVectors_List,coreTensor_?ArrayQ]:=
 Normal@Chop@Fold[
  Dot[#2,#1]&,
  coreTensor,
  Take[leafVectors,Min[Length@leafVectors,TensorRank@coreTensor-1]]
 ]


ContractLeafSSYTCoreTensor::usage="contracts the leftmost modes of coreTensor with symbolic tensors of multiplicity in leafSSYT."
ContractLeafSSYTCoreTensor[leafSSYT_List,coreTensor_?ArrayQ]:=
 With[
  {coreDimensions=Most@Dimensions@coreTensor},
  {leafVectors=MapThread[With[{\[Lambda]=(#1-1)/2},Table[Subscript[Global`x,\[Lambda],m,#2],{m,-\[Lambda],\[Lambda]}]]&,{coreDimensions,Flatten[leafSSYT]}]},
  
  ContractLeafVectorsCoreTensor[leafVectors,coreTensor]
 ]


ContractCoreTensorTrain[coreTensorTrain_List]:=Chop@Dot@@coreTensorTrain


AntisymmetrizeRows[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Antisymmetric/@StandardYoungTableau@p]


SymmetrizeColumns[p_List?VectorQ][tensor_?ArrayQ]:=SymmetrizeColumns[tensor,p]
SymmetrizeColumns[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Symmetric/@ConjugateTableau@StandardYoungTableau@p]


YoungSymmetrize[tensor_?ArrayQ,p_List?VectorQ]:=SymmetrizeColumns[AntisymmetrizeRows[tensor,p],p]


End[];


EndPackage[];
