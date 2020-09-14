## tools for solving two sided equation over exterior algebra
LoadPackage( "ModulePresentations" );
LoadPackage( "RingsForHomalg" );

DeclareGlobalVariable( "WithComments" );
MakeReadWriteGlobal("WithComments");

##
DeclareAttribute( "standard_list_of_basis_indices", IsHomalgRing );
InstallMethod( standard_list_of_basis_indices,
                [ IsHomalgRing and IsExteriorRing ],

function ( R )
local f, new_l,l, n;

if WithComments = true then
    Print( "standard_list_of_basis_indices\n" );
fi;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := Combinations( [ 0 ..n ] );

f := function( l, m )
local new_l;

new_l:= List( l, function( e )

                if Length( e ) = m then 

                   return e;

                else 

                   return [ ];

                fi;

                end );
new_l := Set( new_l );
Remove( new_l, 1 );

return new_l;

end;

new_l := List( [ 1 .. n+1 ], m-> f( l, m ) );

Add( new_l, [ [ ] ], 1 );

return Concatenation( new_l );

end );

##
DeclareGlobalFunction( "ring_element" );
InstallGlobalFunction( ring_element, 

function( l, R )

local f, s,i;

f := RingElementConstructor( R );

s := "1*";

for i in l do 

s := Concatenation( s, "e",String( i ), "*" );

od;

s:= Concatenation( s, "1" );

return f( s, R );

end );

##
DeclareAttribute( "DecompositionOfHomalgMat", IsHomalgMatrix );
InstallMethod( DecompositionOfHomalgMat, 
                 [ IsHomalgMatrix ],
function( d )
local R, n, l, coeff_list, dd, reduction_element, coeff_element, dd_new, u,v, M, m,r;

if WithComments = true then
    Print( "DecompositionOfHomalgMat of ", NrRows(d),"x",NrColumns(d)," homalg matrix \n" );
fi;

dd := ShallowCopy( d );

R := d!.ring;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := standard_list_of_basis_indices( R );

coeff_list := [ ];

for u in l do 

  v := [ 0..n ];
  
  SubtractSet( v, u );
  
  reduction_element := ring_element( v, R );
  
  dd_new := dd*reduction_element;
  
  m := NrColumns( dd_new );
  
  r:= ring_element( Concatenation( u, v ), R );
  
  M := HomalgDiagonalMatrix( List( [ 1 .. m ], i -> r ), R );   
    
  coeff_element := RightDivide( dd_new, M );
 
  Add( coeff_list, [ u, coeff_element ] );
  
  dd := dd - coeff_element*ring_element( u, R );
   
od;

return coeff_list;

end );

Join := function( list, separator )
    local result;
    
    result := Flat( List( list, l -> Concatenation( l, separator ) ) );
    
    Remove( result, Length( result ) );
    
    return result;
end;

BindGlobal( "DecomposeRingElementOverCenter", function( r )
  local R, Q, l, polynomial_vars, polynomial_ring, S, extra_var, r_in_S, part_in_center, result, e_i, part_not_containing_e_i, part_containing_e_i, i;
    
    Assert( 0, false );
  
    R := HomalgRing( r );
    
    Assert( 0, IsExteriorRing( R ) );
    
    Q := CoefficientsRing( R );
    
    l := Length( IndeterminatesOfExteriorRing( R ) );
    
    polynomial_vars := List( [ 1 .. l + 1 ], a -> Concatenation( "x", String( a ) ) );
    
    polynomial_ring := Q * Join( polynomial_vars, "," );
    
    S := KoszulDualRing( polynomial_ring );
    
    extra_var := Concatenation( "e", String( l ) ) / S;
    r_in_S := r/S;
    
    part_in_center := ( (r_in_S * extra_var + extra_var * r_in_S) / (2 * extra_var) ) / R;

    r := r - part_in_center;
    
    result := [ part_in_center ];
    
    for i in [ 0 .. l-1 ] do
        
        e_i := Concatenation( "e", String( i ) ) / R;
        
        part_not_containing_e_i := (r * e_i) / e_i;
        
        part_containing_e_i := r - part_not_containing_e_i;
        
        Add( result, part_containing_e_i / e_i );
        
        r := part_not_containing_e_i;
        
    od;
    
    return result;
    
end );

BindGlobal( "DecomposeMatrixOverCenter", function( M )
  local R, Q, l, polynomial_vars, polynomial_ring, S, extra_var, M_in_S, part_in_center, result, e_i, part_not_containing_e_i, part_containing_e_i, i;
    
    R := HomalgRing( M );
    
    Assert( 0, IsExteriorRing( R ) );
    
    Q := CoefficientsRing( R );
    
    l := Length( IndeterminatesOfExteriorRing( R ) );
    
    polynomial_vars := List( [ 1 .. l + 1 ], a -> Concatenation( "x", String( a ) ) );
    
    polynomial_ring := Q * Join( polynomial_vars, "," );
    
    S := KoszulDualRing( polynomial_ring );
    
    extra_var := Concatenation( "e", String( l ) ) / S;
    M_in_S := M * S;
    
    part_in_center := RightDivide( (M_in_S * extra_var + extra_var * M_in_S), HomalgDiagonalMatrix( ListWithIdenticalEntries( NrColumns( M ), 2 * extra_var ), S ) ) * R;

    M := M - part_in_center;
    
    result := [ part_in_center ];
    
    for i in [ 0 .. l-1 ] do
        
        e_i := Concatenation( "e", String( i ) ) / R;
        
        part_not_containing_e_i := RightDivide( M * e_i, HomalgDiagonalMatrix( ListWithIdenticalEntries( NrColumns( M ), e_i ), R ) );
        
        part_containing_e_i := M - part_not_containing_e_i;
        
        Add( result, RightDivide( part_containing_e_i, HomalgDiagonalMatrix( ListWithIdenticalEntries( NrColumns( M ), e_i ), R ) ) );
        
        M := part_not_containing_e_i;
        
    od;
    
    return UnionOfColumns( result );
    
end );

BindGlobal( "DecomposeMatrixOverQ", function( M )
  local R, Q, l, polynomial_vars, polynomial_ring, S, extra_var, M_in_S, part_in_center, result, e_i, part_not_containing_e_i, part_containing_e_i, i;
    
    R := HomalgRing( M );
    
    Assert( 0, IsExteriorRing( R ) );
    
    Q := CoefficientsRing( R );
    
    l := Length( IndeterminatesOfExteriorRing( R ) );
    
    result := [];
    
    for k in [ 0 .. l ] do
        for comb in Combinations( [ 0 .. l-1 ], k ) do
            generator := Concatenation( "1", Concatenation( List( comb, i -> Concatenation( "*e", String( i ) ) ) ) ) / R;
            adversary := Concatenation( "1", Concatenation( List( Difference( [ 0 .. l-1 ], comb ), i -> Concatenation( "*e", String( i ) ) ) ) ) / R;
            current_part := RightDivide( M * adversary, HomalgDiagonalMatrix( ListWithIdenticalEntries( NrColumns( M ), adversary ), R ) );
            Add( result, RightDivide( current_part, HomalgDiagonalMatrix( ListWithIdenticalEntries( NrColumns( M ), generator ), R ) ) * Q );
            M := M - current_part;
        od;
    od;

    return UnionOfColumns( result );
    
end );

BindGlobal( "MatrixOverRToRealCenter", function( M )
  local entries, new_entries, new_entry, found_e, result, entry, char;

    if NrRows( M ) = 0 or NrColumns( M ) = 0 then
        return HomalgZeroMatrix( NrRows( M ), NrColumns( M ), RealCenter ); 
    fi;
  
    # Error("start MatrixOverRToRealCenter");
  
    # old implementation
    # entries := EntriesOfHomalgMatrix( M );
    # 
    # new_entries := [];
    # 
    # for entry in entries do
    #     new_entry := [];
    #     found_e := false;
    #     for char in String( entry ) do
    #         if char = 'e' then
    #             found_e := not found_e;
    #         fi;
    #         # strip '*' between two e's
    #         if not (found_e and char = '*') then
    #             Add( new_entry, char );
    #         fi;
    #     od;
    #     Add( new_entries, new_entry / RealCenter );
    # od;
    # 
    # result_old := HomalgMatrix( new_entries, NrRows( M ), NrColumns( M ), RealCenter );
    
    # new implementation
    entries := GetListOfHomalgMatrixAsString( M );
    
    new_entries := [];
    
    found_e := false;
    for char in String( entries ) do
        if char = 'e' then
            found_e := not found_e;
        fi;
        # strip '*' between two e's
        if not (found_e and char = '*') then
            Add( new_entries, char );
        fi;
    od;
    
    result := HomalgMatrix( new_entries, NrRows( M ), NrColumns( M ), RealCenter );
    
    # Error("finished MatrixOverRToRealCenter");
    

    return result;
    
end );

BindGlobal( "MatrixOverRealCenterToR", function( M )
  local entries, new_entries, new_entry, found_e, result, entry, char;

    if NrRows( M ) = 0 or NrColumns( M ) = 0 then
        return HomalgZeroMatrix( NrRows( M ), NrColumns( M ), R ); 
    fi;
  
    # old implementation
    entries := EntriesOfHomalgMatrix( M );
    
    new_entries := [];
    
    for entry in entries do
        new_entry := [];
        found_e := false;
        for char in String( entry ) do
            if char = 'e' then
                # add '*' between two e's
                if found_e then
                    Add( new_entry, '*' );
                fi;
                found_e := not found_e;
            fi;
            Add( new_entry, char );
        od;
        Add( new_entries, new_entry / R );
    od;
    
    result_old := HomalgMatrix( new_entries, NrRows( M ), NrColumns( M ), R );

    # new implementation
    entries := GetListOfHomalgMatrixAsString( M );
    
    new_entries := [];
    
    found_e := false;
    for char in String( entries ) do
        if char = 'e' then
            # add '*' between two e's
            if found_e then
                Add( new_entries, '*' );
            fi;
            found_e := not found_e;
        fi;
        Add( new_entries, char );
    od;
    
    result := HomalgMatrix( new_entries, NrRows( M ), NrColumns( M ), R );
    
    Assert( 0, result_old = result );
    
    return result;
    
end );

BindGlobal( "DecomposeMatrixOverRealCenter", function( M )

    return MatrixOverRToRealCenter( DecomposeMatrixOverCenter( M ) );
    
end );

KeyDependentOperation( "FLeftt", IsHomalgMatrix, IsInt, ReturnTrue );
InstallMethod( FLefttOp, [ IsHomalgMatrix, IsInt ],
function( A, m )
local S, basis_indices, zero_matrix,d, e_sigma, sigma;

if WithComments = true then
    Print( "FLefttOp of ", NrRows(A),"x", NrColumns(A)," homalg matrix and m =", m, "\n" );
fi;

#AddToReasons(["left",A,m]);
S := A!.ring;

basis_indices := standard_list_of_basis_indices( S );

d := DecompositionOfHomalgMat( A );

zero_matrix := HomalgZeroMatrix( NrRows(A), NrColumns(A), S );

sigma := basis_indices[ m ];
e_sigma := ring_element( sigma, S );

return UnionOfColumns( List( basis_indices, function( tau )
                            local lambda, m;
                            
                            if ( not IsSubset( sigma, tau ) ) or ( IsSubset( tau, sigma ) and Length( tau ) > Length( sigma ) ) then 
                            
                                return zero_matrix;
                                
                            fi;
                            
                            if tau = sigma then 
                            
                                return d[ 1 ][ 2 ];
                                
                            fi;
                            
                            lambda := ShallowCopy( sigma );
                            
                            SubtractSet( lambda, tau );
                            
                            m := Position( basis_indices, lambda );
                            
                            return  ( ( ring_element( lambda, S )* ring_element( tau, S ) )/e_sigma )*d[ m ][ 2 ];
                            
                            end ) );
                     
end );
 
##
DeclareGlobalFunction( "FLeft" );
InstallGlobalFunction( FLeft,

function( sigma, A )
local p, basis_indices;

if WithComments = true then
    Print( "FLeft of ", NrRows(A),"x", NrColumns(A)," homalg matrix and sigma = ", sigma, "\n" );
fi;

basis_indices := standard_list_of_basis_indices(  A!.ring  );
p := Position( basis_indices, sigma ); 
if HasIsOne( A ) and IsOne( A ) then
	return UnionOfColumns( [ HomalgZeroMatrix(NrRows(A), (p-1)*NrColumns(A), A!.ring ), A, HomalgZeroMatrix( NrRows(A), ( Length(basis_indices) - p )*NrColumns(A), A!.ring)] );
elif HasIsZero( A ) and IsZero( A ) then
	return HomalgZeroMatrix( NrRows(A), NrColumns(A)*Length( basis_indices ), A!.ring );
else
	return FLeftt(A, p);
fi;
end );
  
                  
KeyDependentOperation( "FRightt", IsHomalgMatrix, IsInt, ReturnTrue );
InstallMethod( FRighttOp, [ IsHomalgMatrix, IsInt ],
function( A, m )
local R,basis_indices, zero_matrix,d, e_sigma, sigma;

if WithComments = true then
    Print( "FRighttOp of ", NrRows(A),"x", NrColumns(A)," homalg matrix and m = ", m, "\n" );
fi;
R := A!.ring;
basis_indices := standard_list_of_basis_indices( R );

d := DecompositionOfHomalgMat( A );

zero_matrix := HomalgZeroMatrix( NrRows( A ), NrColumns( A ), R );

sigma := basis_indices[ m ];
e_sigma := ring_element( sigma, R );

return Iterated( List( basis_indices, function( tau )
                            local lambda, m;
                            
                            if ( not IsSubset( sigma, tau ) ) or ( IsSubset( tau, sigma ) and Length( tau ) > Length( sigma ) ) then 
                            
                                return zero_matrix;
                                
                            fi;
                            
                            if tau = sigma then 
                            
                                return d[ 1 ][ 2 ];
                                
                            fi;
                            
                            lambda := ShallowCopy( sigma );
                            
                            SubtractSet( lambda, tau );
                            
                            m := Position( basis_indices, lambda );
                            
                            return  ( ring_element( tau, R )*( ring_element( lambda, R ) )/e_sigma )*d[ m ][ 2 ];
                            
                            end ), UnionOfRows );
                     
end );

##
DeclareGlobalFunction( "FRight" );
InstallGlobalFunction( FRight,

function( sigma, A )
local p, basis_indices;

if WithComments = true then
    Print( "FRight of ", NrRows(A),"x", NrColumns(A)," homalg matrix and sigma = ", sigma, "\n" );
fi;

basis_indices := standard_list_of_basis_indices( A!.ring );
p := Position( basis_indices, sigma ); 
if HasIsOne( A ) and IsOne( A ) then
	return Iterated( [ HomalgZeroMatrix( (p-1)*NrRows(A),NrColumns(A), A!.ring ), A, HomalgZeroMatrix( (Length(basis_indices) - p)*NrRows(A), NrColumns(A), A!.ring)], UnionOfRows );
elif HasIsZero( A ) and IsZero( A ) then
	return HomalgZeroMatrix( NrRows(A)*Length( basis_indices ), NrColumns(A), A!.ring );
else
	return FRightt(A, p);
fi;
end );
