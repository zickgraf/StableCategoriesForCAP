
LoadPackage( "FrobeniusCategoriesForCAP" );
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
  local generating_system, l, i;
    
    generating_system := [ ];
    
    l := Length( Indeterminates( R ) );
    
    for k in [ 0 .. l ] do
        for comb in Combinations( [ 0 .. l-1 ], k ) do
            Add( generating_system, Concatenation( "1", Concatenation( List( comb, i -> Concatenation( "*e", String( i ) ) ) ) ) / R );
        od;
    od;
    
    return generating_system;
    
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
  local generating_system, l, i;
    
    generating_system := [ Identity( R ) ];
    
    l := Length( Indeterminates( R ) );

    for i in [ 0 .. l-1 ] do
        Add( generating_system, Concatenation( "e", String( i ) ) / R );
    od;
    
    return generating_system;
    
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
    
    l := Length( Indeterminates( R ) );

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

    M := Iterated( relations, UnionOfRowsEagerOp );
    
    Eval( M );
    
    #DecideZero( Eval( M ), RealCenter );
    
    SetEval( M, DecideZero( Eval( M ), RealCenter ) );
    
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

SetIsAbelianCategoryWithEnoughInjectives( cat, true );

AddMonomorphismIntoSomeInjectiveObject( cat, 
    function( obj )
    local ring, dual, nat, dual_obj, proj_cover, dual_proj_cover, obj_to_double_dual_obj;
                                                    
    ring := UnderlyingHomalgRing( obj );
    
    dual := FunctorDualLeft( ring );
    
    nat  := NaturalTransformationFromIdentityToDoubleDualLeft( ring );
    
    dual_obj := ApplyFunctor( dual, Opposite( obj ) );
    
    proj_cover := EpimorphismFromSomeProjectiveObject( dual_obj );
    
    dual_proj_cover := ApplyFunctor( dual, Opposite( proj_cover ) );
    
    obj_to_double_dual_obj := ApplyNaturalTransformation( nat, obj );
    
    return PreCompose( obj_to_double_dual_obj, dual_proj_cover );

end );

AddColift( cat, 

    function( morphism_1, morphism_2 )
    local N, M, A, B, I, B_over_M, zero_mat, A_over_zero, sol, XX;

    if WithComments = true then
        Print( "computing Colift of ", NrRows( UnderlyingMatrix(morphism_1) ),"x", NrColumns( UnderlyingMatrix(morphism_1) ), " & ",
                NrRows( UnderlyingMatrix(morphism_2) ),"x", NrColumns( UnderlyingMatrix(morphism_2) ), "\n" );
    fi;
    #                 rxs
    #                I
    #                ꓥ
    #         vxs    | nxs 
    #       ?X      (A)    morphism 2
    #                |
    #                |
    #    uxv    nxv   mxn
    #   M <----(B)-- N
    #
    #      morphism 1
    #
    # We need to solve the system
    #     B*X + Y*I = A
    #     M*X + Z*I = 0
    # i.e.,
    #        [ B ]            [ Y ]        [ A ]
    #        [   ] * X   +    [   ] * I =  [   ]
    #        [ M ]            [ Z ]        [ 0 ]
    #
    # the function is supposed to return X as a ( well defined ) morphism from M to I.
    
    I := UnderlyingMatrix( Range( morphism_2 ) );
    
    N := UnderlyingMatrix( Source( morphism_1 ) );
    
    M := UnderlyingMatrix( Range( morphism_1 ) );
    
    B := UnderlyingMatrix( morphism_1 );
    
    A := UnderlyingMatrix( morphism_2 );
    
    B_over_M := UnionOfRows( B, M );
    
    zero_mat := HomalgZeroMatrix( NrRows( M ), NrColumns( I ), HomalgRing( M ) );
    
    A_over_zero := UnionOfRows( A, zero_mat );

    sol := SolveTwoSidedEquationOverExteriorAlgebra( B_over_M, I, A_over_zero );
    
    if sol= fail then 
    
       return fail;
       
    else 
    
       return PresentationMorphism( Range( morphism_1 ), DecideZeroRows( sol[ 1 ], I ), Range( morphism_2 ) );
       
    fi;
    
end );

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

    RealCenter :=  Q*JoinStringsWithSeparator( vars, "," ) / ideal;
    
    # We need to solve the system
    #     X*B + Y*N = A
    #     P*X + Z*M = 0
    #     I_1*X*B   + I_2*Y*N   + 0_1*Z*0_2 = A
    #     P  *X*I_3 + 0_3*Y*0_4 + I_4*Z*M   = 0_rhs
    # the function is supposed to return X as a ( well defined ) morphism from P to M.

    R_B := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), B ) );

    R_N := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( A ), R ), N ) );

    L_P := MyBlownUpMatrixLeftToRightOverRealCenter( KroneckerMat( TransposedMatrix( P ), HomalgIdentityMatrix( NrColumns( M ), R ) ) );

    R_M := MyBlownUpMatrixOverRealCenter( KroneckerMat( HomalgIdentityMatrix( NrRows( P ), R ), M ) );

    A_vec_rows := v_isom_real_center( A );
    
    # Now we should have
    #   vec_rows( X ) * R_B + vec_rows( Y ) * R_N                      = A_vec_rows
    #   vec_rows( X ) * L_P +                     + vec_row( Z ) * R_M = zero
    #
    # in RealCenter

    mat1 := UnionOfRows( [ R_B, R_N, HomalgZeroMatrix( NrRows( M )*NrRows( P )*(l+1), NrRows( A )*NrColumns( A )*(l+1) , RealCenter ) ] );

    mat2 := UnionOfRows( [ L_P, HomalgZeroMatrix( NrRows( N )*NrColumns( P )*(l+1), NrRows( P )*NrColumns( M )*(l+1), RealCenter ), R_M ] );
    
    mat := UnionOfColumns( mat1, mat2 );

     
    A_vec_rows_zero_vec := UnionOfColumns( A_vec_rows, HomalgZeroMatrix( 1, NrColumns( M )*NrRows( P )*(l+1), RealCenter ) );

    Assert( 0, NrColumns( mat ) = NrColumns( A_vec_rows_zero_vec ) );
    
    matrix_of_relations1 := GetMatrixOfRelationsOverRealCenter( R, NrColumns( mat1 ) / ( l + 1 ) );

    matrix_of_relations2 := GetMatrixOfRelationsOverRealCenter( R, NrColumns( mat2 ) / ( l + 1 ) );
    
    matrix_of_relations := DiagMat( [ matrix_of_relations1, matrix_of_relations2 ] );
    
    Display( Concatenation( "solving ", String( NrRows( mat ) ), "x", String( NrColumns( mat ) ), " (plus ", String( NrRows( matrix_of_relations ) ), " relations) system of equations" ) );

    start_time2 := NanosecondsSinceEpoch();
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
    
    start_time2 := NanosecondsSinceEpoch();
    sol_6 := LeftDivide( mat, A_vec_over_zero_vec );
    Display( Concatenation( "computed LeftDivide in ", String( Float( ( NanosecondsSinceEpoch() - start_time2 ) / 1000 / 1000 / 1000 ) ) ) );

    # Display( "sol_6:" );
    # Display( sol_6 );

    if sol_6 <> fail then
        XX6 := CertainRows( sol_6, [ 1 .. s*v*2^l ] );
        
        XX_6 := UnionOfColumns( List( [ 1 .. v*2^l ], i -> CertainRows( XX6, [ ( i - 1 )*s + 1 .. i*s ] ) ) );

        X_6 := Sum( List( [ 1..2^l ], i-> ( R * CertainColumns( XX_6, [ ( i - 1 )*v + 1 .. i*v ] ) )* ring_element( basis_indices[ i ], R ) ) );

        l6 := PresentationMorphism( Source( morphism_1 ), DecideZeroRows( X_6, M ), Source( morphism_2 ) );
        Assert( 0, IsWellDefined( l6 ) );
        Assert( 0, IsCongruentForMorphisms( PreCompose( l6, morphism_2 ), morphism_1 ) );
    fi;
    
    Display( Concatenation( "computed lift in ", String( Float( ( NanosecondsSinceEpoch() - start_time ) ) / 1000 / 1000 / 1000 ) ) );

    #### evaluation
    if sol_5 = fail and sol_6 = fail then 
      
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

AddIsSplitMonomorphism( cat, 
    function( mor )
    local l;
    l := Colift( mor, IdentityMorphism( Source( mor ) ) );

    if l = fail then 
        return false;
    else 
        return true;
    fi;

end );

AddIsSplitEpimorphism( cat, 
    function( mor )
    local l;
    l := Lift( IdentityMorphism( Range( mor ) ), mor );

    if l = fail then 
        return false;
    else 
        return true;
    fi;

end );


AddIsProjective( cat, 
    function( obj )
     local cover, lift; 
     
     # If the number of rows of the matrix is zero then the module is free, hence projective.
       
     if NrRows( UnderlyingMatrix( obj ) ) = 0 then 
     
       return true;
       
     fi;
     
     cover := EpimorphismFromSomeProjectiveObject( obj );
     
     lift := Lift( IdentityMorphism( obj ), cover );
     
     if lift = fail then 
     
        return false;
       
     fi; 
     
     return true;
     
end );
 
AddIsInjective( cat, IsProjective );

AddCanBeFactoredThroughExactProjective( cat,  
    function( mor )
    local m;
    m := Lift( mor, EpimorphismFromSomeProjectiveObject( Range( mor ) ) );
    if m = fail then
        return false;
    else
        return true;
    fi;
end );

AddCanBeFactoredThroughExactInjective( cat,  
    function( mor )
    local m;
    m := Colift( MonomorphismIntoSomeInjectiveObject( Source( mor ) ), mor );
    if m = fail then
        return false;
    else
        return true;
    fi;
end );

AddFactorizationThroughExactInjective( cat, 
    function( mor )
    local m;
    m := Colift( MonomorphismIntoSomeInjectiveObject( Source( mor ) ), mor );
    if m = fail then
        return fail;
    else
        return [ MonomorphismIntoSomeInjectiveObject( Source( mor ) ), m ];
    fi;
end );

AddFactorizationThroughExactProjective( cat, 
    function( mor )
    local m;
    m := Colift( MonomorphismIntoSomeInjectiveObject( Source( mor ) ), mor );
    if m = fail then
        return fail;
    else
        return [ MonomorphismIntoSomeInjectiveObject( Source( mor ) ), m ];
    fi;
end );

return cat;

end );

basis_of_external_hom := 
    function( MA, MB )
    local A, B, l, basis_indices, Q, N, sN, r,m,s,n,t,sN_t, basis_sN_t, basis, XX, XX_, X_, i, R;

    R := UnderlyingHomalgRing( MA );
    A := UnderlyingMatrix( MA );
    B := UnderlyingMatrix( MB );

    l := Length( IndeterminatesOfExteriorRing( R ) );
    basis_indices := standard_list_of_basis_indices( R );

    Q := CoefficientsRing( R ); 

    N := Q*FF3( A, B );

    if WithComments = true then
        Print( "SyzygiesOfColumns on ", NrRows(N),"x", NrColumns(N)," homalg matrix\n" );
    fi;
    
    sN := SyzygiesOfColumns( N );

    if WithComments = true then
        Print( "done!\n" );
    fi;
    
    r := NrRows( A );
    m := NrColumns( A );
    s := NrColumns( B );
    n := NrRows( B );

    t := m*s*2^l;

    sN_t := CertainRows( sN, [ 1..t ] );
    
    if WithComments = true then
        Print( "SyzygiesOfColumns on ", NrRows(sN_t),"x", NrColumns(sN_t)," homalg matrix\n" );
    fi;
    
    basis_sN_t := BasisOfColumns( sN_t );
    
    if WithComments = true then
        Print( "done!\n" );
    fi;

    basis := [ ];

    for i in [ 1 .. NrColumns( basis_sN_t ) ] do 
        
        XX := CertainColumns( basis_sN_t, [ i ] );

        XX_ := Iterated( List( [ 1 .. s ], i -> CertainRows( XX, [ ( i - 1 )*m*2^l + 1 .. i*m*2^l ] ) ), UnionOfColumns );

        X_ := Sum( List( [ 1..2^l ], i-> ( R*CertainRows( XX_, [ ( i - 1 )*m + 1 .. i*m ] ) )* ring_element( basis_indices[ i ], R ) ) );

        Add( basis, PresentationMorphism( MA, X_, MB ) );

    od;

return DuplicateFreeList( Filtered( basis, b -> not IsZeroForMorphisms(b) ) );

end;

compute_coefficients := function( b, f )
    local R, basis_indices, Q, A, B, C, vec, main_list, matrix, constant, M, N, sol;
    
    M := Source( f );
    N := Range( f );

    if not IsWellDefined( f ) then
        return fail;
    fi;
    
    R := UnderlyingHomalgRing( M );
    basis_indices := standard_list_of_basis_indices( R );
    Q := CoefficientsRing( R ); 
    
    A := List( b, UnderlyingMatrix );
    B := UnderlyingMatrix( N );
    C := UnderlyingMatrix( f );

    vec := function( H ) return Iterated( List( [ 1 .. NrColumns( H ) ], i -> CertainColumns( H, [ i ] ) ), UnionOfRows ); end;

    main_list := 
        List( [ 1 .. Length( basis_indices) ], 
        function( i ) 
        local current_A, current_B, current_C, main;
        current_A := List( A, a -> TransposedMatrix( DecompositionOfHomalgMat(a)[i][2]*Q ) );
        current_B := TransposedMatrix( FRight( basis_indices[i], B )*Q );
        current_C := TransposedMatrix( DecompositionOfHomalgMat(C)[i][2]*Q );
        main := UnionOfColumns( Iterated( List( current_A, vec ), UnionOfColumns ), KroneckerMat( HomalgIdentityMatrix( NrColumns( current_C ), Q ), current_B ) ); 
        return [ main, vec( current_C) ];
        end );

    matrix :=   Iterated( List( main_list, m -> m[ 1 ] ), UnionOfRows );
    constant := Iterated( List( main_list, m -> m[ 2 ] ), UnionOfRows );
    if WithComments = true then
        Print( "LeftDivide on ", NrRows(matrix),"x", NrColumns(matrix)," homalg matrix\n" );
    fi;
    sol := LeftDivide( matrix, constant);
    if sol = fail then 
        return fail;
    else
        return EntriesOfHomalgMatrix( CertainRows( sol, [ 1..Length( b ) ] ) );
    fi;
end;

# Any element, u, in exterior algebra with zero constant is nilpotent.
# In this case u+1 is unit:
# 1 = 1 + u^n = (1+u)( 1+-...+- u^{n-1} ).
is_reduced_module := 
    function( M )
    local F, b;
    F := FreeLeftPresentation( 1, UnderlyingHomalgRing( M ) );
    b := basis_of_external_hom( M, F );
    return not ForAny( b, IsEpimorphism );
end;

colift_lift_in_stable_category :=
    function(alpha_, beta_, gamma_, delta_ )
    local A, B, C, D, alpha, beta, gamma, delta, lambda, I, tau, J, R, l, basis_indices, Q, L_A, L_id_s, L_A_mod, R_C, L_alpha_mod, L_alpha, L_lambda,  
    R_B_2, R_B_1, R_D, R_delta, L_tau, beta_deco, beta_vec, gamma_deco, gamma_vec, R_1, R_2, R_3, C_x, C_y, C_z, C_v, C_g, C_h, C_1, 
    sol, s, v, XX, main_matrix, constants_matrix;
    alpha := UnderlyingMatrix( alpha_);
    beta := UnderlyingMatrix( beta_ );
    gamma := UnderlyingMatrix( gamma_ );
    delta := UnderlyingMatrix( delta_ );
    A := UnderlyingMatrix(   Source( gamma_ ) );
    B := UnderlyingMatrix(  Source( delta_ ) );
    C := UnderlyingMatrix(  Source( alpha_ ) );
    D := UnderlyingMatrix(  Range( gamma_ ) );
    lambda := UnderlyingMatrix(  MonomorphismIntoSomeInjectiveObject( Source( alpha_ ) ) );
    I := UnderlyingMatrix( Range( MonomorphismIntoSomeInjectiveObject(Source(alpha_))));
    tau := UnderlyingMatrix( MonomorphismIntoSomeInjectiveObject( Source( gamma_)));
    J := UnderlyingMatrix( Range( MonomorphismIntoSomeInjectiveObject( Source( gamma_))));

    # We need X,Y,Z,V,G, H such that
    #
    # A     * X                             + V*B                       = 0
    # alpha * X      + lambda * Y + Z * B                               = beta
    #  X    * delta                                   tau * G + H * D   = gamma

    R := HomalgRing( A );
    
    l := Length( IndeterminatesOfExteriorRing( R ) );

    basis_indices := standard_list_of_basis_indices( R );
    
    Q := CoefficientsRing( R );
    
    # X
    L_id_s := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrRows( delta ), Q ), Q*FLeft( u, HomalgIdentityMatrix( NrRows( tau ), R ) ) ) ), UnionOfRows );
    L_A := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, A ) ) ), UnionOfRows );
    L_A_mod :=  L_A* Involution( L_id_s );
    L_alpha := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, alpha ) ) ), UnionOfRows );
    L_alpha_mod :=  L_alpha* Involution( L_id_s );
    R_delta := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, delta ) ), HomalgIdentityMatrix( NrRows( tau ), Q ) ) ), UnionOfRows );
    
    # Y
    L_lambda := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, lambda ) ) ), UnionOfRows );
    
    # Z
    R_B_2 := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, B ) ), HomalgIdentityMatrix( NrRows( alpha ), Q ) ) ), UnionOfRows );
    
    # V
    R_B_1 := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, B ) ), HomalgIdentityMatrix( NrRows( A ), Q ) ) ), UnionOfRows );
    
    # G
    L_tau := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( D ), Q ), Q*FLeft( u, tau ) ) ), UnionOfRows );

    # H
    R_D := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, D ) ), HomalgIdentityMatrix( NrRows( tau ), Q ) ) ), UnionOfRows );
    
    R_1 := NrRows( L_A_mod );
    R_2 := NrRows( L_alpha_mod );
    R_3 := NrRows( R_delta );
    
    C_x := NrColumns( L_A_mod );
    C_y := NrColumns( L_lambda );
    C_z := NrColumns( R_B_2 );
    C_v := NrColumns( R_B_1 );
    C_g := NrColumns( L_tau );
    C_h := NrColumns( R_D );
    C_1 := 1;

    main_matrix := Iterated( 
    [ 
        Iterated( [ L_A_mod, HomalgZeroMatrix(R_1,C_y, Q), HomalgZeroMatrix(R_1,C_z, Q), R_B_1, HomalgZeroMatrix(R_1,C_g, Q), HomalgZeroMatrix(R_1,C_h, Q) ], UnionOfColumns ),
        Iterated( [ L_alpha_mod, L_lambda,R_B_2, HomalgZeroMatrix(R_2,C_v, Q), HomalgZeroMatrix(R_2,C_g, Q), HomalgZeroMatrix(R_2,C_h, Q) ], UnionOfColumns ),
        Iterated( [ R_delta, HomalgZeroMatrix(R_3,C_y, Q), HomalgZeroMatrix(R_3,C_z, Q), HomalgZeroMatrix(R_3,C_v, Q), L_tau, R_D ], UnionOfColumns )
    ], UnionOfRows );

    if IsZero( beta ) then
        beta_vec := HomalgZeroMatrix( R_2, C_1, Q );
    else
        beta_deco := DecompositionOfHomalgMat( beta );
    
        beta_deco := List( beta_deco, i-> i[ 2 ] );

        beta_deco := List( beta_deco, mat -> Iterated( List( [ 1..NrColumns( beta ) ], i-> CertainColumns( mat, [ i ] ) ), UnionOfRows ) );

        beta_vec := Q*Iterated( beta_deco, UnionOfRows );
    fi;

    if IsZero( gamma ) then 
        gamma_vec := HomalgZeroMatrix( R_3, C_1, Q );
    else

        gamma_deco := DecompositionOfHomalgMat( gamma );
   
        gamma_deco := List( gamma_deco, i-> i[ 2 ] );

        gamma_deco := List( gamma_deco, mat -> Iterated( List( [ 1..NrColumns( gamma ) ], i-> CertainColumns( mat, [ i ] ) ), UnionOfRows ) );

        gamma_vec := Q*Iterated( gamma_deco, UnionOfRows );
    fi;

    constants_matrix :=  Iterated( [ HomalgZeroMatrix(R_1, C_1, Q ), beta_vec, gamma_vec ], UnionOfRows );
    
    if WithComments = true then
        Print( "LeftDivide on ", NrRows(main_matrix),"x", NrColumns(main_matrix)," homalg matrix\n" );
    fi;
    
    sol := LeftDivide( main_matrix, constants_matrix );
    
    if sol = fail then 
      
      return fail;
     
    fi;
    
    s := NrColumns( A );
    
    v := NrColumns( B );
    
    XX := CertainRows( sol, [ 1 .. s*v*2^l ] );
    
    XX := UnionOfColumns( List( [ 1 .. v*2^l ], i -> CertainRows( XX, [ ( i - 1 )*s + 1 .. i*s ] ) ) );

    XX := Sum( List( [ 1..2^l ], i-> ( R * CertainColumns( XX, [ ( i - 1 )*v + 1 .. i*v ] ) )* ring_element( basis_indices[ i ], R ) ) );

    return PresentationMorphism( Range( alpha_ ), DecideZeroRows( XX, B ), Range( beta_ ) );
end;
    
all_colift_lift_in_stable_category :=
    function(alpha_, beta_, gamma_, delta_ )
    local A, B, C, D, alpha, beta, gamma, delta, lambda, I, tau, J, R, l, basis_indices, Q, L_A, L_id_s, L_A_mod, R_C, L_alpha_mod, L_alpha, L_lambda,  
    R_B_2, R_B_1, R_D, R_delta, L_tau, beta_deco, beta_vec, gamma_deco, gamma_vec, R_1, R_2, R_3, C_x, C_y, C_z, C_v, C_g, C_h, C_1, 
    sol, s, v, XX, main_matrix, constants_matrix, i, a, K, sy_main_matrix;

    alpha := UnderlyingMatrix( alpha_);
    beta := UnderlyingMatrix( beta_ );
    gamma := UnderlyingMatrix( gamma_ );
    delta := UnderlyingMatrix( delta_ );
    A := UnderlyingMatrix(   Source( gamma_ ) );
    B := UnderlyingMatrix(  Source( delta_ ) );
    C := UnderlyingMatrix(  Source( alpha_ ) );
    D := UnderlyingMatrix(  Range( gamma_ ) );
    lambda := UnderlyingMatrix(  MonomorphismIntoSomeInjectiveObject( Source( alpha_ ) ) );
    I := UnderlyingMatrix( Range( MonomorphismIntoSomeInjectiveObject(Source(alpha_))));
    tau := UnderlyingMatrix( MonomorphismIntoSomeInjectiveObject( Source( gamma_)));
    J := UnderlyingMatrix( Range( MonomorphismIntoSomeInjectiveObject( Source( gamma_))));

    # We need X,Y,Z,V,G, H such that
    #
    # A     * X                             + V*B                       = 0
    # alpha * X      + lambda * Y + Z * B                               = beta
    #  X    * deltaY                                  tau * G + H * D   = gamma

    R := HomalgRing( A );
    
    l := Length( IndeterminatesOfExteriorRing( R ) );

    basis_indices := standard_list_of_basis_indices( R );
    
    Q := CoefficientsRing( R );
    
    # X
    L_id_s := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrRows( delta ), Q ), Q*FLeft( u, HomalgIdentityMatrix( NrRows( tau ), R ) ) ) ), UnionOfRows );
    L_A := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, A ) ) ), UnionOfRows );
    L_A_mod :=  L_A* Involution( L_id_s );
    L_alpha := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, alpha ) ) ), UnionOfRows );
    L_alpha_mod :=  L_alpha* Involution( L_id_s );
    R_delta := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, delta ) ), HomalgIdentityMatrix( NrRows( tau ), Q ) ) ), UnionOfRows );
    
    # Y
    L_lambda := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( B ), Q ), Q*FLeft( u, lambda ) ) ), UnionOfRows );
    
    # Z
    R_B_2 := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, B ) ), HomalgIdentityMatrix( NrRows( alpha ), Q ) ) ), UnionOfRows );
    
    # V
    R_B_1 := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, B ) ), HomalgIdentityMatrix( NrRows( A ), Q ) ) ), UnionOfRows );
    
    # G
    L_tau := Iterated( List( basis_indices, u-> KroneckerMat( HomalgIdentityMatrix( NrColumns( D ), Q ), Q*FLeft( u, tau ) ) ), UnionOfRows );

    # H
    R_D := Iterated( List( basis_indices, u-> KroneckerMat( Involution( Q*FRight( u, D ) ), HomalgIdentityMatrix( NrRows( tau ), Q ) ) ), UnionOfRows );
    
    R_1 := NrRows( L_A_mod );
    R_2 := NrRows( L_alpha_mod );
    R_3 := NrRows( R_delta );
    
    C_x := NrColumns( L_A_mod );
    C_y := NrColumns( L_lambda );
    C_z := NrColumns( R_B_2 );
    C_v := NrColumns( R_B_1 );
    C_g := NrColumns( L_tau );
    C_h := NrColumns( R_D );
    C_1 := 1;

    main_matrix := Iterated( 
    [ 
        Iterated( [ L_A_mod, HomalgZeroMatrix(R_1,C_y, Q), HomalgZeroMatrix(R_1,C_z, Q), R_B_1, HomalgZeroMatrix(R_1,C_g, Q), HomalgZeroMatrix(R_1,C_h, Q) ], UnionOfColumns ),
        Iterated( [ L_alpha_mod, L_lambda,R_B_2, HomalgZeroMatrix(R_2,C_v, Q), HomalgZeroMatrix(R_2,C_g, Q), HomalgZeroMatrix(R_2,C_h, Q) ], UnionOfColumns ),
        Iterated( [ R_delta, HomalgZeroMatrix(R_3,C_y, Q), HomalgZeroMatrix(R_3,C_z, Q), HomalgZeroMatrix(R_3,C_v, Q), L_tau, R_D ], UnionOfColumns )
    ], UnionOfRows );


    if IsZero( beta ) then
        beta_vec := HomalgZeroMatrix( R_2, C_1 );
    else
        beta_deco := DecompositionOfHomalgMat( beta );
    
        beta_deco := List( beta_deco, i-> i[ 2 ] );

        beta_deco := List( beta_deco, mat -> Iterated( List( [ 1..NrColumns( beta ) ], i-> CertainColumns( mat, [ i ] ) ), UnionOfRows ) );

        beta_vec := Q*Iterated( beta_deco, UnionOfRows );
    fi;

    if IsZero( gamma ) then 
        gamma_vec := HomalgZeroMatrix( R_3, C_1);
    else

        gamma_deco := DecompositionOfHomalgMat( gamma );
   
        gamma_deco := List( gamma_deco, i-> i[ 2 ] );

        gamma_deco := List( gamma_deco, mat -> Iterated( List( [ 1..NrColumns( gamma ) ], i-> CertainColumns( mat, [ i ] ) ), UnionOfRows ) );

        gamma_vec := Q*Iterated( gamma_deco, UnionOfRows );
    fi;

    constants_matrix :=  Iterated( [ HomalgZeroMatrix(R_1, C_1, Q ), beta_vec, gamma_vec ], UnionOfRows );

    if WithComments = true then
        Print( "LeftDivide on ", NrRows(main_matrix),"x", NrColumns(main_matrix)," homalg matrix\n" );
    fi;

    sol := LeftDivide( main_matrix, constants_matrix );
    
    if sol = fail then 
      
      return fail;
     
    fi;
    
    s := NrColumns( A );
    
    v := NrColumns( B );
    
    XX := CertainRows( sol, [ 1 .. s*v*2^l ] );
    
    XX := UnionOfColumns( List( [ 1 .. v*2^l ], i -> CertainRows( XX, [ ( i - 1 )*s + 1 .. i*s ] ) ) );

    XX := Sum( List( [ 1..2^l ], i-> ( R * CertainColumns( XX, [ ( i - 1 )*v + 1 .. i*v ] ) )* ring_element( basis_indices[ i ], R ) ) );

    K := [ ];

    sy_main_matrix := BasisOfColumns( CertainRows( SyzygiesOfColumns( main_matrix ), [ 1 .. s*v*2^l ] ) );

    for i in [ 1 .. NrColumns( sy_main_matrix ) ] do 

        a := CertainColumns( sy_main_matrix, [ i ] );
    
        a := UnionOfColumns( List( [ 1 .. v*2^l ], i -> CertainRows( a, [ ( i - 1 )*s + 1 .. i*s ] ) ) );

        a := Sum( List( [ 1..2^l ], i-> ( R * CertainColumns( a, [ ( i - 1 )*v + 1 .. i*v ] ) )* ring_element( basis_indices[ i ], R ) ) );
    
        a := PresentationMorphism( Range( alpha_ ), DecideZeroRows( a, B ), Range( beta_ ) );

        if not IsZeroForMorphisms( a ) then 
            Add( K, a );
        fi;
    od;

    return [ PresentationMorphism( Range( alpha_ ), DecideZeroRows( XX, B ), Range( beta_ ) ), K ];
end;

# Very important note:
# if you compute hom(M,N) you will have a set of 46 morphisms and the first and the 30'th are congruent.
# h := generating_set_of_external_hom(M,N);
# gap> IsCongruentForMorphisms( h[1], h[30] );
# true
# gap> Display( h[1] );
# e1,0,0,0,0,
# 0, 0,0,0,0,
# 0, 0,0,0,0,
# 0, 0,0,0,0,
# 0, 0,0,0,0 

# A morphism in Category of left presentations of Q{e0,e1}
# gap> Display( h[30] );
# 0,0,0,e0*e1,0,
# 0,0,0,0,    0,
# 0,0,0,0,    0,
# 0,0,0,0,    0,
# 0,0,0,0,    0 

# methods for stable category

# -5*e0*e1-7*e0+2*e1-8,-6*e0*e1+8*e0-4*e1-8,6*e0*e1+10*e0-3*e1+5,
# 10*e0*e1+e0+7*e1-2,  -e0*e1-8*e0+4*e1-6,  -e0*e1-e0+e1+2       

# A projective object in Category of left presentations of Q{e0,e1}
