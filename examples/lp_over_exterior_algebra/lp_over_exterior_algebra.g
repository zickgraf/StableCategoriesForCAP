
#LoadPackage( "FrobeniusCategories" );
ReadPackage( "StableCategoriesForCAP", "/examples/lp_over_exterior_algebra/tools.g" );


RealCenter := fail;

###########################################
# center


DeclareAttribute( "GeneratingSystemOverCenter", IsHomalgRing );

InstallMethod( GeneratingSystemOverCenter, [ IsHomalgRing ], function( R )
  local generating_system, l, i;
    
    generating_system := [ Identity( R ) ];
    
    l := Length( Indeterminates( R ) );

    for i in [ 0 .. l-1 ] do
        Add( generating_system, Concatenation( "e", String( i ) ) / R );
    od;
    
    return generating_system;
    
end );

MyBlownUpMatrixOverCenter := function( M )
  local R, generating_system_over_center, l;
    
    R := HomalgRing( M );
    
    generating_system_over_center := GeneratingSystemOverCenter( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_center, generator -> DecomposeMatrixOverCenter( generator * M ) ) );
    
end;

MyBlownUpMatrixLeftToRightOverCenter := function( M )
  local R, generating_system_over_center, l;
    
    R := HomalgRing( M );
    
    generating_system_over_center := GeneratingSystemOverCenter( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_center, generator -> DecomposeMatrixOverCenter( M * generator ) ) );
    
end;

MyReducedVectorOverCenter := function( R, M )
  local l, m, n, generating_system_over_center, result;
    
    l := Length( Indeterminates( R ) );

    m := NrRows( M );
    n := NrColumns( M ) / (l+1);
    Assert( 0, IsInt( n ) );

    if m = 0 or n = 0 then
        return HomalgZeroMatrix( m, n, R );
    fi;

    generating_system_over_center := GeneratingSystemOverCenter( R );
    
    result := Sum( [ 1 .. l+1 ], i -> CertainColumns( M, [ (i-1)*n+1 .. i * n ] ) * generating_system_over_center[i] );
    
    Assert( 0, NrRows( result ) = m );
    Assert( 0, NrColumns( result ) = n );

    return result;
end;

GetMatrixOfRelationsOverCenter := function( R, dimension )
  local zero_relation, index_of_dth_ith_basis_vector, l, relations, relation, d, i, j, k;
    
    zero_relation := function()
        return ListWithIdenticalEntries( (l + 1) * dimension, "0" );
    end;
  
    index_of_dth_ith_basis_vector := function( d, i )
        return dimension * i + d;
    end;
    
    l := Length( Indeterminates( R ) );

    relations := [  ];
    
    for d in [ 1 .. dimension ] do
        for i in [ 1 .. l ] do
            for j in [ 1 .. l ] do
                if i < j then
                    relation := zero_relation();
                    relation[index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( i - 1 ), "*e", String( j - 1 ) );
                    Add( relations, relation );
                    for k in [ 1 .. l ] do
                        if k <> i and k <> j then
                            relation := zero_relation();
                            relation[index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( k - 1 ), "*e", String( j - 1 ) );
                            relation[index_of_dth_ith_basis_vector( d, j )] := Concatenation( "e", String( k - 1 ), "*e", String( i - 1 ) );
                            Add( relations, relation );
                        fi;
                    od;
                fi;
                if i > j then
                    relation := zero_relation();
                    relation[index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( j - 1 ), "*e", String( i - 1 ) );
                    Add( relations, relation );
                fi;
            od;
        od;
    od;
    
    return HomalgMatrix( relations, Length( relations ), (l + 1) * dimension, R );
end;

###########################################
# over Q

DeclareAttribute( "GeneratingSystemOverQ", IsHomalgRing );

InstallMethod( GeneratingSystemOverQ, [ IsHomalgRing ], function( R )
  local generating_system, indets, l, k, comb;
    
    generating_system := [ One( R ) ];
    
    indets := Indeterminates( R );
    
    l := Length( indets );
    
    for k in [ 1 .. l ] do
        for comb in Combinations( indets, k ) do
            Add( generating_system, Product( comb ) );
        od;
    od;
    
    return generating_system;
    
end );

DeclareAttribute( "GeneratingSystemOverQToRealCenterTrafoMatrix", IsHomalgRing );

InstallMethod( GeneratingSystemOverQToRealCenterTrafoMatrix, [ IsHomalgRing ], function( R )
  local generating_system, l, i, k, comb, real_center_comb;
    
    generating_system := [ ];
    
    l := Length( Indeterminates( R ) );
    l_Q := Length( GeneratingSystemOverQ( R ) );
    
    for j in [ 1 .. l_Q ] do
        generating_system[j] := ListWithIdenticalEntries( l + 1, Zero( RealCenter ) );
    od;
    
    j := 1;
    for k in [ 0 .. l ] do
        for comb in Combinations( [ 0 .. l-1 ], k ) do
            if Length( comb ) mod 2 = 0 then
                real_center_comb := comb;
                index := 1;
            else
                real_center_comb := comb{ [ 2 .. Length( comb ) ] };
                index := comb[1] + 2;
            fi;
            real_center_string := "1";
            for i in [ 1 .. Length( real_center_comb ) / 2 ] do
                real_center_string := Concatenation( real_center_string, "*e", String( real_center_comb[2*i-1] ), "e", String( real_center_comb[2*i] ) );
            od;
            generating_system[j][index] := real_center_string / RealCenter;
            j := j + 1;
        od;
    od;
    
    return HomalgMatrix( generating_system, l_Q, l + 1, RealCenter );
    
end );

MyBlownUpMatrixOverQ := function( M )
  local R, generating_system_over_Q, l;
    
    R := HomalgRing( M );
    
    generating_system_over_Q := GeneratingSystemOverQ( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_Q, generator -> DecomposeMatrixOverQ( generator * M ) ) );
    
end;

MyBlownUpMatrixLeftToRightOverQ := function( M )
  local R, generating_system_over_Q, l;
    
    R := HomalgRing( M );
    
    generating_system_over_Q := GeneratingSystemOverQ( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_Q, generator -> DecomposeMatrixOverQ( M * generator ) ) );
    
end;

MyReducedVectorOverQ := function( R, M )
  local l, m, n, generating_system_over_Q, result;
    
    l := Length( Indeterminates( R ) );

    m := NrRows( M );
    n := NrColumns( M ) / (2^l);
    Assert( 0, IsInt( n ) );

    if m = 0 or n = 0 then
        return HomalgZeroMatrix( m, n, R );
    fi;

    generating_system_over_Q := GeneratingSystemOverQ( R );
    
    result := Sum( [ 1 .. 2^l ], i -> ( CertainColumns( M, [ (i-1)*n+1 .. i * n ] ) * R ) * generating_system_over_Q[i] );
    
    Assert( 0, NrRows( result ) = m );
    Assert( 0, NrColumns( result ) = n );

    return result;
end;

GetMatrixOfRelationsOverQ := function( R, dimension )
  local l;
    
    l := Length( Indeterminates( R ) );

    Q := CoefficientsRing( R ); 

    return HomalgZeroMatrix( 0, (2^l) * dimension, Q );
end;

###########################################
# real center


DeclareAttribute( "GeneratingSystemOverRealCenter", IsHomalgRing );

InstallMethod( GeneratingSystemOverRealCenter, [ IsHomalgRing ], function( R )
    
    return Concatenation( [ One( R ) ], Indeterminates( R ) );
    
end );

MyBlownUpMatrixOverRealCenter := function( M )
  local R, generating_system_over_center, l;
    
    R := HomalgRing( M );
    
    generating_system_over_center := GeneratingSystemOverRealCenter( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_center, generator -> DecomposeMatrixOverRealCenter( generator * M ) ) );
    
end;

MyBlownUpMatrixLeftToRightOverRealCenter := function( M )
  local R, generating_system_over_center, l;
    
    R := HomalgRing( M );
    
    generating_system_over_center := GeneratingSystemOverRealCenter( R );
    
    l := Length( Indeterminates( R ) );

    return UnionOfRows( List( generating_system_over_center, generator -> DecomposeMatrixOverRealCenter( M * generator ) ) );
    
end;

MyReducedVectorOverRealCenter := function( R, M )
  local l, m, n, generating_system_over_center, result;
    
    l := Length( Indeterminates( R ) );

    m := NrRows( M );
    n := NrColumns( M ) / (l+1);
    Assert( 0, IsInt( n ) );

    if m = 0 or n = 0 then
        return HomalgZeroMatrix( m, n, R );
    fi;

    generating_system_over_center := GeneratingSystemOverRealCenter( R );

    M := MatrixOverRealCenterToR( M );
    
    result := Sum( [ 1 .. l+1 ], i -> CertainColumns( M, [ (i-1)*n+1 .. i * n ] ) * generating_system_over_center[i] );
    
    Assert( 0, NrRows( result ) = m );
    Assert( 0, NrColumns( result ) = n );

    return result;
end;

GetMatrixOfRelationsOverRealCenter := function( R, dimension )
  local zero_relation, index_of_dth_ith_basis_vector, l, relations, relation, M, d, i, j, k;
    
    zero_relation := function()
        return HomalgInitialMatrix( 1, (l + 1) * dimension, RealCenter );
    end;
  
    index_of_dth_ith_basis_vector := function( d, i )
        return dimension * i + d;
    end;
    
    indets := Indeterminates( R );
    
    l := Length( indets );
    
    relations := [  ];
    
    for d in [ 1 .. dimension ] do
        for i in [ 1 .. l ] do
            for j in [ 1 .. l ] do
                if i < j then
                    relation := zero_relation();
                    relation[1,index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( i - 1 ), "e", String( j - 1 ) ) / RealCenter;
                    Add( relations, relation );
                    for k in [ 1 .. l ] do
                        if k <> i and k <> j then
                            relation := zero_relation();
                            if k < j then
                                relation[1,index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( k - 1 ), "e", String( j - 1 ) ) / RealCenter;
                            else
                                relation[1,index_of_dth_ith_basis_vector( d, i )] := Concatenation( "-e", String( j - 1 ), "e", String( k - 1 ) ) / RealCenter;
                            fi;
                            if k < i then
                                relation[1,index_of_dth_ith_basis_vector( d, j )] := Concatenation( "e", String( k - 1 ), "e", String( i - 1 ) ) / RealCenter;
                            else
                                relation[1,index_of_dth_ith_basis_vector( d, j )] := Concatenation( "-e", String( i - 1 ), "e", String( k - 1 ) ) / RealCenter;
                            fi;
                            Add( relations, relation );
                        fi;
                    od;
                fi;
                if i > j then
                    relation := zero_relation();
                    relation[1,index_of_dth_ith_basis_vector( d, i )] := Concatenation( "e", String( j - 1 ), "e", String( i - 1 ) ) / RealCenter;
                    Add( relations, relation );
                fi;
            od;
        od;
    od;

    # recursion depth trap
    # Display("got here1");
    # M := UnionOfColumns( relations );
    # Error("asd");
    # Display("got here2");
    # Eval( M );
    # Display("got here3");
    # 
    # return M;

    #M := Iterated( relations, UnionOfRowsEager );
    
    M := UnionOfRows( relations );
    
    Eval( M );
    
    #DecideZero( Eval( M ), RealCenter );
    
    # MODIFIED
    #SetEval( M, DecideZero( Eval( M ), RealCenter ) );
    
    # DecideZero( A, RealCenter );
    
    return M;
    # return HomalgMatrix( relations, Length( relations ), (l + 1) * dimension, RealCenter );
end;
################################

BindGlobal( "ADD_METHODS_TO_LEFT_PRESENTATIONS_OVER_EXTERIOR_ALGEBRA", 

function( cat )
local R;

R := cat!.ring_for_representation_category;

if HasIsFinalized( cat ) then
    Error( "The category should be not-finalized to be able to add methods" );
fi;

v_isom_center := function( A )
    return DecomposeMatrixOverCenter( vec_rows( A ) );
end;

v_isom_inv_center := function( R, X, s, v )
  local vec_X;
    
    vec_X := MyReducedVectorOverCenter( R, X );
    
    return devec_rows( vec_X, s, v );
end;

v_isom_Q := function( A )
    return DecomposeMatrixOverQ( vec_rows( A ) );
end;

v_isom_inv_Q := function( R, X, s, v )
  local vec_X;
    
    vec_X := MyReducedVectorOverQ( R, X );

    return devec_rows( vec_X, s, v );
end;

v_isom_real_center := function( A )
    return DecomposeMatrixOverRealCenter( vec_rows( A ) );
end;

v_isom_inv_real_center := function( R, X, s, v )
  local vec_X;
    
    vec_X := MyReducedVectorOverRealCenter( R, X );
    
    return devec_rows( vec_X, s, v );
end;

if true then

AddLift( cat, 

  function( morphism_1, morphism_2 )
    local P, M, N, r, s, u, v, m, n, A, B, R, l, basis_indices, Q, sol, R_B, R_N, L_P, R_M, bu_A, A_vec, mat1, mat2, mat, A_vec_over_zero_vec, sol_2, XX2, vec_X_2, X_2, l2, matrix_of_relations, left_coeffs, right_coeffs, start_time, sol_3, XX3, vec_X_3, X_3, l3, L_id_s, L_P_mod, A_deco, A_deco_list, A_deco_list_vec, sol_4, XX4, XX_4, X_4, l4, X;
   
    DeactivateToDoList();
    
    if WithComments = true then
        Print( "computing Lift of ", NrRows( UnderlyingMatrix(morphism_1) ),"x", NrColumns( UnderlyingMatrix(morphism_1) ), " & ",
                NrRows( UnderlyingMatrix(morphism_2) ),"x", NrColumns( UnderlyingMatrix(morphism_2) ), "\n" );
    fi;
    #                 rxs
    #                P
    #                |
    #         sxv    | sxn
    #        X      (A)   morphism_1
    #                |
    #                V
    #    uxv    vxn   mxn
    #   M ----(B)--> N
    #
    #     morphism_2
    #
    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.
    
    
    P := UnderlyingMatrix( Source( morphism_1 ) );
    
    M := UnderlyingMatrix( Source( morphism_2 ) );

    N := UnderlyingMatrix( Range( morphism_2 ) );
    
    r := NrRows( P );
    s := NrColumns( P );
    
    u := NrRows( M );
    v := NrColumns( M );
    
    m := NrRows( N );
    n := NrColumns( N );
    
    A := UnderlyingMatrix( morphism_1 );
    
    B := UnderlyingMatrix( morphism_2 );
    
    R := HomalgRing( A );

    l := Length( IndeterminatesOfExteriorRing( R ) );
    
    basis_indices := standard_list_of_basis_indices( R );

    Assert( 0, 2^l = Length( basis_indices ) );
    
    Q := CoefficientsRing( R ); 

    if IsZero( P ) then
        sol := RightDivide( A, UnionOfRows(B,N) );
        if sol = fail then 
            return fail;
        else 
            return PresentationMorphism( Source( morphism_1 ), DecideZeroRows( CertainColumns( sol, [1..NrRows(B) ] ), M ), Source( morphism_2 ) );
        fi;
    fi;

    #### my first implementation
    Display("#### my first implementation");

    # M := HomalgMatrix( "[[1+2*e0+3*e1+4*e0*e1,5+6*e0+7*e1+8*e0*e1], [9+10*e0+11*e1+12*e0*e1,13+14*e0+15*e1+16*e0*e1]]", 2, 2, R );
    # Display( MyBlownUpMatrix( M ) );
    # Error();
    
    # I_1 := HomalgIdentityMatrix( s, R );
    # I_2 := HomalgIdentityMatrix( s, R );
    # I_3 := HomalgIdentityMatrix( v, R );
    # I_4 := HomalgIdentityMatrix( r, R );
    # 0_1 := HomalgZeroMatrix( s, r, R );
    # 0_2 := HomalgZeroMatrix( u, n, R );
    # 0_3 := HomalgZeroMatrix( r, s, R );
    # 0_4 := HomalgZeroMatrix( m, v, R );
    # 
    # 0_rhs := HomalgZeroMatrix( r, v, R );

    # bu_I_1 := MyBlownUpMatrix( I_1 );
    # bu_I_2 := MyBlownUpMatrix( I_2 );
    # bu_I_3 := MyBlownUpMatrix( I_3 );
    # bu_I_4 := MyBlownUpMatrix( I_4 );
    # bu_0_1 := MyBlownUpMatrix( 0_1 );
    # bu_0_2 := MyBlownUpMatrix( 0_2 );
    # bu_0_3 := MyBlownUpMatrix( 0_2 );
    # bu_0_3 := MyBlownUpMatrix( 0_3 );
    # bu_0_4 := MyBlownUpMatrix( 0_4 );
    # bu_B := MyBlownUpMatrix( B );
    # bu_N := MyBlownUpMatrix( N );
    # bu_P := MyBlownUpMatrix( P );
    # bu_M := MyBlownUpMatrix( M );
    # bu_A := MyBlownUpMatrix( A );
    # bu_0_rhs := MyBlownUpMatrix( 0_rhs );
    
    # bu_sol := SolveTwoSidedLinearSystem( [[bu_I_1,bu_I_2,bu_0_1],[bu_P,bu_0_3,bu_I_4]], [[bu_B,bu_N,bu_0_2],[bu_I_3,bu_0_4,bu_M]], [ bu_A, bu_0_rhs ] );
    # bu_sol := SolveTwoSidedLinearSystem( [[bu_I_1,bu_I_2],[bu_P,bu_0_3]], [[bu_B,bu_N],[bu_I_3,bu_0_4]], [ bu_A, bu_0_rhs ] );
    
    # sol := List( bu_sol, x -> MyReducedMatrix( R, x ) );

    
    #### my second implementation
    Display("#### my second implementation");

    if false then
    
    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.

    R_B := MyBlownUpMatrixRightToLeftOverQ( KroneckerMat( TransposedMatrix( B ), HomalgIdentityMatrix( NrRows( A ), R ) ) );

    if not IsZero( N ) then 
        R_N := MyBlownUpMatrixRightToLeftOverQ( KroneckerMat( TransposedMatrix( N ), HomalgIdentityMatrix( NrRows( A ), R ) ) );
    fi;

    L_P := MyBlownUpMatrixOverQ( KroneckerMat( HomalgIdentityMatrix( NrColumns( M ), R ), P ) );

    R_M := MyBlownUpMatrixRightToLeftOverQ( KroneckerMat( TransposedMatrix( M ), HomalgIdentityMatrix( NrRows( P ), R ) ) );

    bu_A := MyBlownUpMatrixOverQ( A );
    bu_A := CertainColumns( bu_A, [ 0 .. (NrColumns( A ) - 1) ] * 2^l + 1 );
    
    A_vec := vec( bu_A );
    
    # Now we should have 
    #   R_B     * vec( X ) + R_N * vec( Y )                  = vec_A
    #   L_P_mod * vec( X ) +                + R_M * vec( Z ) = zero
    
    # or  [   R_B    R_N     0  ]      [  vec( X ) ]        [ vec_A ]
    #     [                     ]  *   [  vec( Y ) ]   =    [       ]
    #     [ L_P_mod  0      R_M ]      [  vec( Z ) ]        [   0   ]
    #
    # in the underlying field Q

    if not IsZero( N ) then

        mat1 := UnionOfColumns( [ R_B, R_N, HomalgZeroMatrix( NrRows( A )*NrColumns( A )*2^l, NrRows( M )*NrRows( P )*2^l, Q ) ] );
    
        mat2 := UnionOfColumns( [ L_P, HomalgZeroMatrix( NrRows( P )*NrColumns( M )*2^l, NrRows( N )*NrColumns( P )*2^l, Q ), R_M ] );
    
    else
        
        mat1 := UnionOfColumns( R_B, HomalgZeroMatrix( NrRows( A )*NrColumns( A )*2^l, NrRows( M )*NrRows( P )*2^l, Q ) );
    
        mat2 := UnionOfColumns( L_P, R_M );
    
    fi;

    mat := UnionOfRows( mat1, mat2 );
     
    A_vec_over_zero_vec := UnionOfRows( A_vec, HomalgZeroMatrix( NrColumns( M )*NrRows( P )*2^l, 1, Q ) );

    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " system of equations" ) );
    # Display( mat );
    # Display( A_vec_over_zero_vec );
    
    sol_2 := LeftDivide( mat, A_vec_over_zero_vec );

    # Display( "sol_2:" );
    # Display( sol_2 );
    
    if sol_2 <> fail then
        XX2 := CertainRows( sol_2, [ 1 .. s*v*2^l ] );

        vec_X_2 := MyReducedVectorOverQ( R, XX2 );
        
        X_2 := devec( vec_X_2, s, v );

        l2 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_2, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l2 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l2, morphism_2 ), morphism_1 ) );
    fi;

    fi;
    
    #### my third implementation
    Display("#### my third implementation");

    if false then
    
    start_time := NanosecondsSinceEpoch();

    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.

    R_B := MyBlownUpMatrixOverCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), B ) );

    R_N := MyBlownUpMatrixOverCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), N ) );

    L_P := MyBlownUpMatrixLeftToRightOverCenter( KroneckerMat( TransposedMatrix( P ), HomalgIdentityMatrix( NrColumns( M ), R ) ) );

    R_M := MyBlownUpMatrixOverCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( P ), R ), M ) );

    A_vec_rows := v_isom_center( A );
    
    # Now we should have
    #   vec_rows( X ) * R_B + vec_rows( Y ) * R_N                      = A_vec_rows
    #   vec_rows( X ) * L_P +                     + vec_row( Z ) * R_M = zero
    #
    # in Center( R )

    mat1 := UnionOfRows( [ R_B, R_N, HomalgZeroMatrix( NrRows( M )*NrRows( P )*(l+1), NrRows( A )*NrColumns( A )*(l+1) , R ) ] );

    mat2 := UnionOfRows( [ L_P, HomalgZeroMatrix( NrRows( N )*NrColumns( P )*(l+1), NrRows( P )*NrColumns( M )*(l+1), R ), R_M ] );
    
    mat := UnionOfColumns( mat1, mat2 );
     
    A_vec_rows_zero_vec := UnionOfColumns( A_vec_rows, HomalgZeroMatrix( 1, NrColumns( M )*NrRows( P )*(l+1), R ) );

    Assert( 0, NrColumns( mat ) = NrColumns( A_vec_rows_zero_vec ) );
    
    matrix_of_relations1 := GetMatrixOfRelationsOverCenter( R, NrColumns( mat1 ) / ( l + 1 ) );

    matrix_of_relations2 := GetMatrixOfRelationsOverCenter( R, NrColumns( mat2 ) / ( l + 1 ) );

    matrix_of_relations := DiagMat( [ matrix_of_relations1, matrix_of_relations2 ] );
    
    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " (plus relations) system of equations" ) );
    # voidm := HomalgVoidMatrix( R );
    # # asd := BasisOfRowsCoeff( UnionOfRows( mat, matrix_of_relations ), voidm );
    # Eval(asd);
    # 
    # Error("aaaaaaaaaaaaaa");
    
    start_time2 := NanosecondsSinceEpoch();
    sol_3 := RightDivide( A_vec_rows_zero_vec, UnionOfRows( mat, matrix_of_relations ) );
    Display( Concatenation( "computed RightDivide in ", String( Float( ( NanosecondsSinceEpoch() - start_time2 ) / 1000 / 1000 / 1000 ) ) ) );

    # Display( "sol_3:" );
    # Display( sol_3 );
    
    if sol_3 <> fail then
        XX3 := CertainColumns( sol_3, [ 1 .. s*v*(l+1) ] );

        X_3 := v_isom_inv_center( R, XX3, s, v );
        
        l3 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_3, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l3 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l3, morphism_2 ), morphism_1 ) );
    fi;

    Display( Concatenation( "computed lift in ", String( Float( ( NanosecondsSinceEpoch() - start_time ) / 1000 / 1000 / 1000 ) ) ) );
    
    fi;
    
    #### my implementation over Q
    Display("#### my implementation over Q");

    if false then
    
    start_time := NanosecondsSinceEpoch();

    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.

    R_B := MyBlownUpMatrixOverQ( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), B ) );

    if not IsZero( N ) then 
        R_N := MyBlownUpMatrixOverQ( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), N ) );
    fi;

    L_P := MyBlownUpMatrixLeftToRightOverQ( KroneckerMat( TransposedMatrix( P ), HomalgIdentityMatrix( NrColumns( M ), R ) ) );

    R_M := MyBlownUpMatrixOverQ( KroneckerMat( HomalgIdentityMatrix( NrRows( P ), R ), M ) );

    A_vec_rows := v_isom_Q( A );
    
    # Now we should have
    #   vec_rows( X ) * R_B + vec_rows( Y ) * R_N                      = A_vec_rows
    #   vec_rows( X ) * L_P +                     + vec_row( Z ) * R_M = zero
    #
    # in Q( R )

    if not IsZero( N ) then

        mat1 := UnionOfRows( [ R_B, R_N, HomalgZeroMatrix( NrRows( M )*NrRows( P )*(2^l), NrRows( A )*NrColumns( A )*(2^l), Q ) ] );
    
        mat2 := UnionOfRows( [ L_P, HomalgZeroMatrix( NrRows( N )*NrColumns( P )*(2^l), NrRows( P )*NrColumns( M )*(2^l), Q ), R_M ] );
    
    else
        
        mat1 := UnionOfRows( R_B, HomalgZeroMatrix( NrRows( M )*NrRows( P )*(2^l), NrRows( A )*NrColumns( A )*(2^l), Q ) );
    
        mat2 := UnionOfRows( L_P, R_M );
    
    fi;

    mat := UnionOfColumns( mat1, mat2 );
     
    A_vec_rows_zero_vec := UnionOfColumns( A_vec_rows, HomalgZeroMatrix( 1, NrColumns( M )*NrRows( P )*(2^l), Q ) );

    Assert( 0, NrColumns( mat ) = NrColumns( A_vec_rows_zero_vec ) );
    
    matrix_of_relations1 := GetMatrixOfRelationsOverQ( R, NrColumns( mat1 ) / ( 2^l ) );

    matrix_of_relations2 := GetMatrixOfRelationsOverQ( R, NrColumns( mat2 ) / ( 2^l ) );

    matrix_of_relations := DiagMat( [ matrix_of_relations1, matrix_of_relations2 ] );

    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " (plus relations) system of equations" ) );

    start_time2 := NanosecondsSinceEpoch();
    sol_4 := RightDivide( A_vec_rows_zero_vec, UnionOfRows( mat, matrix_of_relations ) );
    Display( Concatenation( "computed RightDivide in ", String( Float( ( NanosecondsSinceEpoch() - start_time2 ) / 1000 / 1000 / 1000 ) ) ) );

    # Display( "sol_4:" );
    # Display( sol_4 );
    
    if sol_4 <> fail then
        XX4 := CertainColumns( sol_4, [ 1 .. s*v*(2^l) ] );

        X_4 := v_isom_inv_Q( R, XX4, s, v );
        
        l4 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_4, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l4 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l4, morphism_2 ), morphism_1 ) );
    fi;

    Display( Concatenation( "computed lift in ", String( Float( ( NanosecondsSinceEpoch() - start_time ) / 1000 / 1000 / 1000 ) ) ) );
    
    fi;
    
    #### my implementation over real center
    Display("#### my implementation over real center");

    if true then
    
    start_time := NanosecondsSinceEpoch();

    
    indets := Indeterminates( R );
    
    vars := [];
    vars_by_index := [];

    for i in [ 0 .. (l-1) ] do
        for j in [ (i+1) .. (l-1) ] do
             Add( vars, Concatenation( "e", String(i), "e", String(j) ) );
             Add( vars_by_index, [ i, j ] );
        od;
    od;

    ideal := [];
    for i in [ 1 .. Length( vars_by_index ) ] do
        var1 := vars_by_index[ i ];

        Add( ideal, Concatenation( "e", String(var1[1]), "e", String(var1[2]), "^2" ) );
        
        for j in [ (i+1) .. Length( vars_by_index ) ] do
            var2 := vars_by_index[ j ];

            if var1[1] = var2[1] then
                result := "0";
            else 
                # var1[1] < var2[1]
                if var2[1] < var1[2] then
                    if var2[2] < var1[2] then
                        result := Concatenation( "e", String(var1[1]), "e", String(var2[1]), "*e", String(var2[2]), "e", String(var1[2]) );
                    elif var2[2] = var1[2] then
                        result := "0";
                    else
                        # var2[2] > var1[2]
                        result := Concatenation( "-e", String(var1[1]), "e", String(var2[1]), "*e", String(var1[2]), "e", String(var2[2]) );
                    fi;
                elif var2[1] = var1[2] then
                    result := "0";
                else
                    # var2[1] > var1[2]
                    result := false;
                fi;
            fi;
            
            if result <> false then
                Add( ideal, Concatenation( "e", String(var1[1]), "e", String(var1[2]), "*e", String(var2[1]), "e", String(var2[2]), "-(", result, ")" ) );
            fi;
        od;
    od;

    #RealCenter :=  Q*JoinStringsWithSeparator( vars, "," ) / ideal;
    #RealCenter :=  Q*JoinStringsWithSeparator( vars, "," );
    RealCenter :=  HomalgQRingInSingular( Q*JoinStringsWithSeparator( vars, "," ), ideal );

# AdditiveClosure
if false then

    #Cfpres := LeftPresentations( RealCenter );

    add_hom_structure_to_CR := function( )
      local ring, equality_func, Cfpres, matrix_of_relations, R_as_C_module, Q, l, polynomial_vars, polynomial_ring, S, extra_var, e, decompose_element_over_real_center, sets, t_obj, elements, size, RG, HOM_PERMUTATION_ARRAY, i, decompose_element_over_Q, generating_system_over_Q_as_matrix, matrix_element_as_morphism, list_list_as_matrix;
        Display( "define homomorphism structure of the delooping over real center" );
        
        Cfpres := LeftPresentations( RealCenter : overhead := false );

        DeactivateToDoList();
        
        DeactivateCachingOfCategory(Cfpres);
        CapCategorySwitchLogicOff(Cfpres);
        DisableSanityChecks(Cfpres);
        
        # R as C module
        matrix_of_relations := GetMatrixOfRelationsOverRealCenter( R, 1 );
        R_as_C_module := AsLeftPresentation( matrix_of_relations );
        
        Q := CoefficientsRing( R );
        
        indets := Indeterminates( R );
        
        l := Length( indets );
        
        generating_system_over_real_center := GeneratingSystemOverRealCenter( R );
        generating_system_over_Q := GeneratingSystemOverQ( R );
        generating_system_over_Q_to_real_center_trafo_matrix := GeneratingSystemOverQToRealCenterTrafoMatrix( R );
        generating_system_over_Q_as_matrix := HomalgMatrix( generating_system_over_Q, Length( generating_system_over_Q ), 1, R );

        decompose_element_over_real_center := function( r )
          local coefficients_over_Q, coefficients_over_real_center, i, index, k, comb;
            
            if IsZero( r ) then
                return HomalgZeroMatrix( 1, l+1, RealCenter );
            fi;
          
            coefficients_over_Q := CoefficientsWithGivenMonomials( r, generating_system_over_Q_as_matrix );
            
            #coefficients_over_real_center :=  CoercedMatrix(coefficients_over_Q, RealCenter) * generating_system_over_Q_to_real_center_trafo_matrix;
            coefficients_over_real_center :=  (coefficients_over_Q * RealCenter) * generating_system_over_Q_to_real_center_trafo_matrix;
            
            return coefficients_over_real_center;
            
            #return HomalgMatrix( coefficients_over_real_center, 1, l+1, RealCenter );
            
        end;
        
        ring_map_real_center_to_R := RingMap( List( vars_by_index, x -> indets[x[1] + 1] * indets[x[2] + 1] ), RealCenter, R);

        #return RingAsCategory( R : FinalizeCategory := false, HomomorphismStructureOverSubringOfCenter := [ R_as_C_module, generating_system_over_real_center, decompose_element_over_real_center, ring_map_real_center_to_R ] );
        
        MatrixCategory( Q : overhead := false );

        R_as_Q_vector_space := VectorSpaceObject( Length( generating_system_over_Q ), Q );

        mycounter := 0;

        decompose_element_over_Q := function( r )
          local coefficients_over_Q, coefficients_over_real_center, i, index, k, comb;
            #% CAP_JIT_RESOLVE_FUNCTION
            
            #if not IsHomalgMatrix( r ) then
            #    r := HomalgMatrix( [ r ], 1, 1, R );
            #fi;

            #return CoercedMatrix( UnionOfColumns( ListWithIdenticalEntries( Length( generating_system_over_Q ) , r ) ), Q );

            #if IsZero( r ) then
            #    return CoercedMatrix( HomalgZeroMatrix( 1, Length( generating_system_over_Q ), R ), Q );
            #fi;

            #mycounter := mycounter + 1;
          
            coefficients_over_Q := CoefficientsWithGivenMonomials( HomalgMatrix( [ r ], 1, 1, R ), generating_system_over_Q_as_matrix );
            
            return coefficients_over_Q * Q;
            
            #return CoercedMatrix( coefficients_over_Q, Q );
            
        end;
        
        ring_map_Q_to_R := RingMap( [], Q, R );
        
        #return RingAsCategory( R : FinalizeCategory := false, overhead := false, HomomorphismStructureOverSubringOfCenter := [ R_as_C_module, generating_system_over_real_center, decompose_element_over_real_center, ring_map_real_center_to_R ] );
        return RingAsCategory( R : FinalizeCategory := false, overhead := false, HomomorphismStructureOverSubringOfCenter := [ R_as_Q_vector_space, generating_system_over_Q, decompose_element_over_Q, ring_map_Q_to_R ] );
        
    end;
    
    CR := add_hom_structure_to_CR( );

    DeactivateCachingOfCategory(CR);
    CapCategorySwitchLogicOff(CR);
    DisableSanityChecks(CR);
        
    Finalize( CR );

    BindGlobal( "GlobalR", R );

    matrix_element_as_morphism := function( r )
        #% CAP_JIT_RESOLVE_FUNCTION
        return RingAsCategoryMorphismOp( RingAsCategory( GlobalR ), r );
    end;

    #ERows := AdditiveClosure( CR : matrix_element_as_morphism := r -> RingAsCategoryMorphismOp( RingAsCategory( GlobalR ), HomalgMatrix( [ r ], 1, 1, GlobalR ) ) );
    #ERows := AdditiveClosure( CR : matrix_element_as_morphism := matrix_element_as_morphism, enable_compilation := true );
    ERows := AdditiveClosure( CR : matrix_element_as_morphism := matrix_element_as_morphism, enable_compilation := [ "HomomorphismStructureOnMorphismsWithGivenObjects" ] );
    #ERows := AdditiveClosure( CR : matrix_element_as_morphism := matrix_element_as_morphism );

    DeactivateCachingOfCategory(ERows);
    CapCategorySwitchLogicOff(ERows);
    DisableSanityChecks(ERows);
        
    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.
    
    nr_rows_X := NrRows( A );
    nr_cols_X := NrRows( B );
    nr_rows_Y := NrRows( A );
    nr_cols_Y := NrRows( N );
    nr_rows_Z := NrRows( P );
    nr_cols_Z := NrRows( M );
    
    left_coeffs  := [ [ HomalgIdentityMatrix( nr_rows_X, R ), HomalgIdentityMatrix( nr_rows_Y, R )            , HomalgZeroMatrix( NrRows( A ), nr_rows_Z, R )    ],
                      [ P                                   , HomalgZeroMatrix( NrRows( P ), nr_rows_Y, R )   , HomalgIdentityMatrix( nr_rows_Z, R )             ]
                    ];

    right_coeffs := [ [ B                                   , N                                               , HomalgZeroMatrix( nr_cols_Z, NrColumns( A ), R ) ],
                      [ HomalgIdentityMatrix( nr_cols_X, R ), HomalgZeroMatrix( nr_cols_Y, NrColumns( M ), R ), M                                                ]
                    ];

    right_hand_side := [ A, HomalgZeroMatrix( NrRows( P ), NrColumns( M ), R ) ];

    matrix_to_additive_closure_morphism := function( M )
      local unique_object, source, range, matrix, i, j;
        
        if IsList( M ) then
            return List( M, matrix_to_additive_closure_morphism );
        fi;
        
        unique_object := RingAsCategoryUniqueObject( RingAsCategory( R ) );

        source := AdditiveClosureObject( ListWithIdenticalEntries( NrRows( M ), unique_object ), AdditiveClosure( RingAsCategory( R ) ) );
        range := AdditiveClosureObject( ListWithIdenticalEntries( NrCols( M ), unique_object ), AdditiveClosure( RingAsCategory( R ) ) );
        
        return AdditiveClosureMorphism( source, M, range );
        
    end;
    
    left_coeffs := matrix_to_additive_closure_morphism( left_coeffs );
    right_coeffs := matrix_to_additive_closure_morphism( right_coeffs );
    right_hand_side := matrix_to_additive_closure_morphism( right_hand_side );

    Display( "now solving linear system" );

    SetInfoLevel( InfoCapJit, 1 );
    
    #homalgIOMode( "d" );

    # TraceAllMethods();
    solution := SolveLinearSystemInAbCategory( left_coeffs, right_coeffs, right_hand_side );

    Y := MorphismMatrix( solution[1] );
    #Y := [];
    #for i in [ 1 .. Length( X ) ] do
    #    Y[i] := [];
    #    for j in [ 1 .. Length( X[1] ) ] do
    #        Y[i][j] := UnderlyingRingElement( X[i,j] );
    #    od;
    #od;
    
    l5 := PresentationMorphism( Source( morphism_1 ), HomalgMatrix( Y, R ), Source( morphism_2 ) );
    Assert( 0, IsWellDefined( l5 ) );
    Assert( 0, IsCongruentForMorphisms( PreCompose( l5, morphism_2 ), morphism_1 ) );
    
    Error( "ERows" );

fi;
    
    Display("asd1");
    R_B := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), B ) );

    Display("asd2");
    R_N := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), N ) );

    Display("asd3");
    L_P := MyBlownUpMatrixLeftToRightOverRealCenter( KroneckerMat( TransposedMatrix( P ), HomalgIdentityMatrix( NrColumns( M ), R ) ) );

    Display("asd4");
    R_M := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( P ), R ), M ) );

    Display("asd5");
    A_vec_rows := v_isom_real_center( A );
    
    # Now we should have
    #   vec_rows( X ) * R_B + vec_rows( Y ) * R_N                      = A_vec_rows
    #   vec_rows( X ) * L_P +                     + vec_row( Z ) * R_M = zero
    #
    # in RealCenter

    Display("asd6");
    mat1 := UnionOfRows( [ R_B, R_N, HomalgZeroMatrix( NrRows( M )*NrRows( P )*(l+1), NrRows( A )*NrColumns( A )*(l+1) , RealCenter ) ] );

    Display("asd7");
    mat2 := UnionOfRows( [ L_P, HomalgZeroMatrix( NrRows( N )*NrColumns( P )*(l+1), NrRows( P )*NrColumns( M )*(l+1), RealCenter ), R_M ] );
    
    mat := UnionOfColumns( mat1, mat2 );

     
    Display("asd8");
    A_vec_rows_zero_vec := UnionOfColumns( A_vec_rows, HomalgZeroMatrix( 1, NrColumns( M )*NrRows( P )*(l+1), RealCenter ) );

    Display("asd9");
    Assert( 0, NrColumns( mat ) = NrColumns( A_vec_rows_zero_vec ) );
    
    Display("asd10");
    matrix_of_relations1 := GetMatrixOfRelationsOverRealCenter( R, NrColumns( mat1 ) / ( l + 1 ) );

    Display("asd11");
    matrix_of_relations2 := GetMatrixOfRelationsOverRealCenter( R, NrColumns( mat2 ) / ( l + 1 ) );
    
    Display("asd12");
    matrix_of_relations := DiagMat( [ matrix_of_relations1, matrix_of_relations2 ] );
    
    Display("asd13");
    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " (plus ", String( NrRows( matrix_of_relations ) ), " relations) system of equations" ) );

    start_time2 := NanosecondsSinceEpoch();

    #Error("asd");
    #homalgIOMode( "d" );
    sol_5 := RightDivide( A_vec_rows_zero_vec, UnionOfRows( mat, matrix_of_relations ) );
    Display( Concatenation( "computed RightDivide in ", String( Float( ( NanosecondsSinceEpoch() - start_time2 ) / 1000 / 1000 / 1000 ) ) ) );

    # Display( "sol_5:" );
    # Display( sol_5 );

    if sol_5 = fail then
        Display( "there exists no lift" );
    else
        Display( "there exists a lift" );
        XX5 := CertainColumns( sol_5, [ 1 .. s*v*(l+1) ] );

        X_5 := v_isom_inv_real_center( R, XX5, s, v );
        
        l5 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_5, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l5 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l5, morphism_2 ), morphism_1 ) );
    fi;

    Display( Concatenation( "computed lift in ", String( Float( ( NanosecondsSinceEpoch() - start_time ) / 1000 / 1000 / 1000 ) ) ) );
    
    fi;

    #### Kamal's implementation
    Display("#### Kamal's implementation");

    start_time := NanosecondsSinceEpoch();

    Display("asd1");
    R_B := UnionOfRows( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, B ) ), HomalgIdentityMatrix( NrRows( A ), Q ) ) ) );

    Display("asd2");
    if not IsZero( N ) then 
        R_N := UnionOfRows( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, N ) ), HomalgIdentityMatrix( NrRows( A ), Q ) ) ) );    
    fi;

    Display("asd3");
    L_P := UnionOfRows( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( M ), Q ), Q*FLeft( u, P ) ) ) );

    Display("asd4");
    R_M := UnionOfRows( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, M ) ), HomalgIdentityMatrix( NrRows( P ), Q ) ) ) );

    Display("asd5");
    L_id_s := UnionOfRows( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrRows( B ), Q ), Q*FLeft( u, HomalgIdentityMatrix( NrRows( A ), R ) ) ) ) );

    Display("asd6");
    L_P_mod := L_P * Involution( L_id_s );

    Display("asd7");
    A_deco := DecompositionOfHomalgMat( A );
   
    Display("asd8");
    A_deco_list := List( A_deco, i-> i[ 2 ] );

    Display("asd9");
    A_deco_list_vec := List( A_deco_list, mat -> UnionOfRows( List( [ 1..NrColumns( A ) ], i-> CertainColumns( mat, [ i ] ) ) ) );

    Display("asd10");
    A_vec := Q*UnionOfRows( A_deco_list_vec );
    
    
    # Now we should have 
    #   R_B     * vec( X ) + R_N * vec( Y )                  = vec_A
    #   L_P_mod * vec( X ) +                + R_M * vec( Z ) = zero
    
    # or  [   R_B    R_N     0  ]      [  vec( X ) ]        [ vec_A ]
    #     [                     ]  *   [  vec( Y ) ]   =    [       ]
    #     [ L_P_mod  0      R_M ]      [  vec( Z ) ]        [   0   ]
    #
    # in the underlying field Q
    
    if not IsZero( N ) then
    
        mat1 := UnionOfColumns( [ R_B, R_N, HomalgZeroMatrix( NrRows( A )*NrColumns( A )*2^l, NrRows( M )*NrRows( P )*2^l, Q ) ] );
    
        mat2 := UnionOfColumns( [ L_P_mod, HomalgZeroMatrix( NrRows( P )*NrColumns( M )*2^l, NrRows( N )*NrColumns( P )*2^l, Q ), R_M ] );
    
    else
        
        mat1 := UnionOfColumns( R_B, HomalgZeroMatrix( NrRows( A )*NrColumns( A )*2^l, NrRows( M )*NrRows( P )*2^l, Q ) );
    
        mat2 := UnionOfColumns( L_P_mod, R_M );
    
    fi;

    mat := UnionOfRows( mat1, mat2 );
     
    A_vec_over_zero_vec := UnionOfRows( A_vec, HomalgZeroMatrix( NrColumns( M )*NrRows( P )*2^l, 1, Q ) );

    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " system of equations" ) );
    #Display( mat );
    #Display( A_vec_over_zero_vec );
    
    
    #mynumberofrows := 1625;
    #mat := CertainRows( mat, [ 1 .. mynumberofrows ] );
    #A_vec_over_zero_vec := CertainRows( A_vec_over_zero_vec, [ 1 .. mynumberofrows ] );
    #rationals_gap := HomalgFieldOfRationals();
    #mat := mat * rationals_gap;
    #A_vec_over_zero_vec := A_vec_over_zero_vec * rationals_gap;
    
    Eval( mat );
    Eval( A_vec_over_zero_vec );
    
    start_time2 := NanosecondsSinceEpoch();
    sol_6 := LeftDivide( mat, A_vec_over_zero_vec );
    Display( Concatenation( "computed LeftDivide in ", String( Float( ( NanosecondsSinceEpoch() - start_time2 ) / 1000 / 1000 / 1000 ) ) ) );

    # Display( "sol_6:" );
    # Display( sol_6 );

    if sol_6 = fail then
        Display( "there exists no lift" );
    else
        Display( "there exists a lift" );
        XX6 := CertainRows( sol_6, [ 1 .. s*v*2^l ] );
        
        XX_6 := UnionOfColumns( List( [ 1 .. v*2^l ], i -> CertainRows( XX6, [ ( i - 1 )*s + 1 .. i*s ] ) ) );

        X_6 := Sum( List( [ 1..2^l ], i-> ( R * CertainColumns( XX_6, [ ( i - 1 )*v + 1 .. i*v ] ) )* ring_element( basis_indices[ i ], R ) ) );

        l6 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_6, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l6 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l6, morphism_2 ), morphism_1 ) );
    fi;
    
    Display( Concatenation( "computed lift in ", String( Float( ( NanosecondsSinceEpoch() - start_time ) ) / 1000 / 1000 / 1000 ) ) );

    #### evaluation
    if sol_6 = fail then 
      
        Display( fail );
        
      return fail;
     
    fi;

    # Assert( 0, sol_2 <> fail );
    # Assert( 0, sol_3 <> fail );
    # Assert( 0, sol_4 <> fail );
    Assert( 0, sol_5 <> fail );
    Assert( 0, sol_6 <> fail );

    X := X_5;
    Display(X);
    
    # X := sol[1];
    # Y := sol[2];
    # Z := sol[3];
    
    
    # Assert( 0, I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A     );
    # Assert( 0, P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs );
    # Assert( 0, X*B + Y*N = A     );
    # Assert( 0, P*X + Z*M = 0_rhs );

    return PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X, M ), Source( morphism_2 ) );
    
end );

fi;

return cat;

end );

