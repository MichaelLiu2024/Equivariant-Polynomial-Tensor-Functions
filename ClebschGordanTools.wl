(* ::Package:: *)

BeginPackage["ClebschGordanTools`",{"CombinatoricsTools`","IsotypicDecompositionTools`","TensorTools`"}];


TensorTrainBasisTensorProduct
TensorTrainBasisExteriorPower
TensorTrainBasisSymmetricPower
TensorTreeBasisSchurPower


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


(*helper function that converts the index \[Alpha] to the corresponding spin \[Gamma]*)
indicesToPaths[\[Gamma]_Integer?NonNegative,{\[Lambda]_Integer?NonNegative,\[Alpha]_Integer?NonNegative}]:=Abs[\[Gamma]-\[Lambda]]+\[Alpha]-1


ClebschGordanTensor::usage="gives the elementary Clebsch-Gordan tensor coupling \[Lambda]1 and \[Lambda]2 to \[Lambda]3."
ClebschGordanTensor[\[Lambda]1_Integer?NonNegative,\[Lambda]2_Integer?NonNegative,\[Lambda]3_Integer?NonNegative]:=
 ClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3]=
  Chop@SparseArray[
   Join@@Table[
    {1+\[Lambda]1+m1,1+\[Lambda]2+m2,1+\[Lambda]3+m1+m2}->N@ClebschGordan[{\[Lambda]1,m1},{\[Lambda]2,m2},{\[Lambda]3,m1+m2}],
    {m1,-\[Lambda]1,\[Lambda]1},
    {m2,Max[-\[Lambda]2,-\[Lambda]3-m1],Min[\[Lambda]2,\[Lambda]3-m1]}
   ],
   {2\[Lambda]1+1,2\[Lambda]2+1,2\[Lambda]3+1}
 ]


(*add checking functions ValidPathQ[\[Lambda]1,\[Lambda]2,\[Lambda]3] for above*)
(**)


ValidPathQ[\[Lambda]s_List,\[Gamma]s_List]:=
 VectorQ[\[Lambda]s,NonNegativeIntegerQ]\[And]
 VectorQ[\[Gamma]s,NonNegativeIntegerQ]\[And]
 Length@\[Lambda]s==Length@\[Gamma]s\[And]
 First@\[Lambda]s==First@\[Gamma]s\[And]
 If[Length@\[Lambda]s>=2,Abs[ListConvolve[{1,-1},\[Gamma]s]]\[VectorLessEqual]Rest[\[Lambda]s]\[VectorLessEqual]ListConvolve[{1,1},\[Gamma]s],True]


ClebschGordanTensorTrain::usage="gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]/;ValidPathQ[\[Lambda]s,\[Gamma]s]:=
 If[
  Length@\[Lambda]s==1,
  {1},
  MapThread[ClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]
 ]


PathBasisTensorProduct::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s."
PathBasisTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=
 SortBy[
  Map[
   Function[indices,FoldList[indicesToPaths,First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],indices}]]],
   Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]
  ],
  FreeQ[Most@#,0]&(*move all paths containing a zero to the left*)
 ]


(* ::Subsection:: *)
(*Public Functions*)


TensorTrainBasisTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=ClebschGordanTensorTrain[\[Lambda]s]/@PathBasisTensorProduct[\[Lambda]s,\[Mu]]


(*add input checks below for evenness/oddness of \[Gamma]2!*)


TensorTrainBasisExteriorPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold exterior power of \[Lambda]."
SetAttributes[TensorTrainBasisExteriorPower,Listable]
TensorTrainBasisExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;
 d<=3:=
  Switch[
   d,
   1,{{1}},
   2,{{ClebschGordanTensor[\[Lambda],\[Lambda],\[Mu]]}},
   3,{ClebschGordanTensorTrain[{\[Lambda],\[Lambda],\[Lambda]},{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}]}
  ]


TensorTrainBasisSymmetricPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda]."
SetAttributes[TensorTrainBasisSymmetricPower,Listable]
TensorTrainBasisSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;
 d<=3:=
  Switch[
   d,
   1,{{1}},
   2,{{ClebschGordanTensor[\[Lambda],\[Lambda],\[Mu]]}},
   3,{ClebschGordanTensorTrain[{\[Lambda],\[Lambda],\[Lambda]},{\[Lambda],#+Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}]}
  ]


TensorTrainBasisSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d>=4:=
 Module[
  {
  interiorPaths,
  interiorTensorTrains,
  interiorRandomProbes,
  syndromeMatrix
  },
  
  interiorPaths=
   Select[
    PathBasisTensorProduct[ConstantArray[\[Lambda],d],\[Mu]],
    EvenQ@#[[2]]&(*ensures that the original tensor is not Antisymmetric[{1,2}]*)
   ];
  
  interiorTensorTrains=ClebschGordanTensorTrain[ConstantArray[\[Lambda],d]]/@interiorPaths;
  
  interiorRandomProbes=RandomReal[1,{d+d(*oversampling*),2\[Lambda]+1}];
  
  syndromeMatrix=
   Flatten[
    Outer[EvaluateSymmetrizedTensorTrain,interiorTensorTrains,interiorRandomProbes,1],
    {{2,3},{1}}(*level 3 contains the vectors of syndromes*)
   ];
  
  interiorTensorTrains[[PivotColumns@syndromeMatrix]]
 ]


(*these expensive functions need to be memoized, since they are evaluated multiple times*)
TensorTreeBasisSchurPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the image of the Young symmetrizer p on \[Lambda]."
TensorTreeBasisSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]:=
 With[
  {d=Total@p},
  Switch[
   Length@p,
   0,<||>,
   1,<|"interiorTensorTrains"->({1}&/@#),"leafObjects"->List/@#|>&@TensorTrainBasisExteriorPower[\[Lambda],d,\[Mu]],
   d,<|"interiorTensorTrains"->#,"leafObjects"->(ConstantArray[{1},d]&/@#)|>&@TensorTrainBasisSymmetricPower[\[Lambda],d,\[Mu]],
   _,
   Module[
    {
     interiorSpins,
     interiorTensorTrains,
     leafTensorTrains,
     leafRandomProbes,
     interiorRandomProbes,
     syndromeMatrix,
     linearIndices,
     interiorDimensions,
     leafDimensions,
     totalDimensions,
     interiorSpinsIndices,
     tensorTrainIndices
    },
    
    interiorSpins=
     SortBy[
      ConstrainedIsotypicComponentsExteriorPowers[\[Lambda],p,\[Mu]],
      FreeQ[#,0]&
     ];
    
    (*
    Level 1: interiorSpins
    Level 2: basis element
    Object:  tensor train
    *)
    interiorTensorTrains=TensorTrainBasisTensorProduct[#,\[Mu]]&/@interiorSpins;

    (*
    Level 1: interiorSpins
    Level 2: part of partition
    Level 3: basis element
    Object:  tensor train
    *)
    leafTensorTrains=TensorTrainBasisExteriorPower[\[Lambda],p,#]&/@interiorSpins;
    
    (*
    Level 1: random probe
    Object:  list of First@p random vectors in Subscript[H, \[Lambda]]
    *)
    leafRandomProbes=RandomReal[1,{d+d(*oversampling*),First@p,2\[Lambda]+1}];
    
    (*
    Level 1: interiorSpins
    Level 2: part of partition
    Level 3: basis element
    Level 4: random probe
    Object:  syndrome vector
    *)
    interiorRandomProbes=Outer[EvaluateAntisymmetrizedTensorTrain,leafTensorTrains,leafRandomProbes,3,1];
    
    (*
    Level 1: interiorSpins
    Level 2: random probe
    Level 3: part of partition
    Level 4: basis element
    Object:  syndrome vector
    *)
    interiorRandomProbes=Transpose[interiorRandomProbes,{1,3,4,2}];
    
    (*
    Level 1: interiorSpins
    Level 2: basis element
    Level 3: random probe
    Level 4: basis element
    Object:  syndrome vector
    *)
    syndromeMatrix=
     MapThread[
      Function[
       {interiorTensorTrain,interiorRandomProbe},
       Outer[EvaluateTensorTrain,interiorTensorTrain,Tuples/@interiorRandomProbe,1,2]
      ],
      {interiorTensorTrains,interiorRandomProbes}
     ];
    
    syndromeMatrix=Flatten[syndromeMatrix,{{3,5},{1,2,4}}];
    
    linearIndices=PivotColumns@syndromeMatrix;
    
    (*prioritize paths with 0 to include in the basis*)
    (*perm=OrderingBy[Flatten[interiorTensorTrains,1],FreeQ[Most@#,0]&];
    linearIndices=perm[[PivotColumns@syndromeMatrix[[All,perm]]]];*)
    
    interiorDimensions=Length/@interiorTensorTrains;
    leafDimensions=Map[Length,leafTensorTrains,{2}];
    totalDimensions=MapThread[Prepend,{leafDimensions,interiorDimensions}];
    
    {interiorSpinsIndices,tensorTrainIndices}=
     Transpose@MapApply[
      {#1,linearIndexToArrayMultiIndex[#2,totalDimensions[[#1]]]}&,
      linearIndicesToRaggedMultiIndices[linearIndices,interiorDimensions*MapApply[Times,leafDimensions]]
     ];
    
    <|
     "interiorTensorTrains"->MapThread[interiorTensorTrains[[#1,First@#2]]&,{interiorSpinsIndices,tensorTrainIndices}],
     "leafObjects"->MapThread[MapThread[Part,{leafTensorTrains[[#1]],Rest@#2}]&,{interiorSpinsIndices,tensorTrainIndices}]
    |>
   ]
  ]
 ]


linearIndicesToRaggedMultiIndices[linearIndices_List?VectorQ,dimensions_List?VectorQ]/;Max@linearIndices<=Total@dimensions:=
 With[
  {accumulateDimensions=Prepend[Accumulate@dimensions,0]},
  {i=Flatten[FirstPosition[accumulateDimensions,total_/;#<=total]&/@linearIndices]-1},
  {j=linearIndices-accumulateDimensions[[i]]},
  
  Transpose@{i,j}
 ]


linearIndexToArrayMultiIndex[linearIndex_Integer?Positive,dimensions_List?VectorQ]/;linearIndex<=Times@@dimensions:=
 IntegerDigits[linearIndex-1,MixedRadix@dimensions,Length@dimensions]+1


End[];


EndPackage[];
