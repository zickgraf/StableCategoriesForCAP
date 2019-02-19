LoadPackage( "StableCategoriesForCAP" );
ReadPackage( "StableCategoriesForCAP", "/examples/lp_over_exterior_algebra/lp_over_exterior_algebra.g" );

BindGlobal( "ADD_METHODS_TO_STABLE_CAT_OF_LEFT_PRESENTATIONS_OVER_EXTERIOR_ALGEBRA",

function( category )

##
AddLiftColift( category,
    function( alpha, beta, gamma, delta )
    local lift;
    lift := colift_lift_in_stable_category( 
            UnderlyingUnstableMorphism( alpha ), 
            UnderlyingUnstableMorphism( beta ), 
            UnderlyingUnstableMorphism( gamma ), 
            UnderlyingUnstableMorphism( delta ) 
            );
    if lift = fail then
        return fail;
    else
        return AsStableMorphism( lift );
    fi;
    
    end );

## Since we have LiftColift, we automatically have Lifts & Colifts (see Derivations in Triangulated categories).
##
AddIsSplitMonomorphism( category, 
    function( mor )
    local l;
    l := Colift( mor, IdentityMorphism( Source( mor ) ) );

    if l = fail then
        AddToReasons( "IsSplitMonomorphism: because the morphism can not be coliftet to the identity morphism of the source" ); 
        return false;
    else 
        return true;
    fi;

end );

AddIsSplitEpimorphism( category,
    function( mor )
    local l;
    l := Lift( IdentityMorphism( Range( mor ) ), mor );

    if l = fail then 
        AddToReasons( "IsSplitMonomorphism: because the morphism can not be coliftet to the identity morphism of the source" );
        return false;
    else 
        return true;
    fi;

end );

AddInverseImmutable( category,
    function( mor )
    return Lift( IdentityMorphism( Range( mor ) ), mor );
end );

end );

WithComments := true;

R := KoszulDualRing( HomalgFieldOfRationalsInSingular()*"x,y" );
cat := LeftPresentations( R: FinalizeCategory := false );
ADD_METHODS_TO_LEFT_PRESENTATIONS_OVER_EXTERIOR_ALGEBRA( cat );
TurnAbelianCategoryToExactCategory( cat );
SetIsFrobeniusCategory( cat, true );
Finalize( cat );

SetTestFunctionForStableCategories(cat, CanBeFactoredThroughExactProjective );
stable_cat := StableCategory( cat );
SetIsTriangulatedCategory( stable_cat, true );
ADD_METHODS_TO_STABLE_CAT_OF_LEFT_PRESENTATIONS_OVER_EXTERIOR_ALGEBRA( stable_cat );
AsTriangulatedCategory( stable_cat );
Finalize( stable_cat );

m := HomalgMatrix( "[ [ e1, e0, e1, e1*e0, e0-e1 ], [ 0, 1, e1*e0, 0, -4*e1 ], [ e1+e0, 0, 1, e1*e0-e1, 0 ] ]", 3, 5, R );
m := AsLeftPresentation( m );
M := AsStableObject( m );
n := HomalgMatrix( "[ [ e1*e0, e0-e1 ], [ 1, e0 ], [ e1*e0, e1*e0-e0 ] ]", 3, 2, R );
n := HomalgMatrix( "[ [ e0 ] ]", 1, 1, R );
n := AsLeftPresentation( n );
N := AsStableObject( n );
p := HomalgMatrix( "[ [ 1, 0, e1+e0, 0, 0 ], [ 0, 1, e0, 0, e0*e1 ], [ 0, 0, 1, e1, e0 ] ]", 3, 5, R );
p := AsLeftPresentation( p );
# P := AsStableObject( p );


#Assert( 0, IsZero( IdentityMorphism( M ) ) = false );
# Assert( 0, IsZero( IdentityMorphism( N ) ) = false );

#l := Lift( IdentityMorphism( p ), EpimorphismFromSomeProjectiveObject( p ) );
#Assert( 0, UnderlyingMatrix( l ) = HomalgMatrix( "[ [ 0,0,0,e0*e1,-e0*e1 ], [ 0,0,0,e0*e1,-e0*e1 ], [ 0,0,0,-e1,  -e0 ], [ 0,0,0,1,    0 ], [ 0,0,0,0,    1 ] ]", 5, 5, R ) );

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

R := KoszulDualRing( HomalgFieldOfRationalsInSingular()*"x" );
cat := LeftPresentations( R: FinalizeCategory := false );
ADD_METHODS_TO_LEFT_PRESENTATIONS_OVER_EXTERIOR_ALGEBRA( cat );
TurnAbelianCategoryToExactCategory( cat );
SetIsFrobeniusCategory( cat, true );
Finalize( cat );

p := HomalgMatrix( "[ [ 1 ] ]", 1, 1, R );
P := AsLeftPresentation( p );

n := HomalgMatrix( "[ [ 1 ] ]", 1, 1, R );
n := HomalgMatrix( "[ [ 1 ] ]", 1, 1, R );
N := AsLeftPresentation( n );

m := HomalgMatrix( "[ [ 1, 1 ] ]", 1, 2, R );
M := AsLeftPresentation( m );

a := HomalgMatrix( "[ [ 1 ] ]", 1, 1, R );
A := PresentationMorphism( P, a, N );

b := HomalgMatrix( "[ [ 1 ], [ 1 ] ]", 2, 1, R );
B := PresentationMorphism( M, b, N );

Assert( 0, IsWellDefined( A ) );
Assert( 0, IsWellDefined( B ) );

Display("asd");
Lift( A, B );

Display("qwe");
