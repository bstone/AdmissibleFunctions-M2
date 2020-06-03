newPackage(
	"AdmissibleFunctions",
    	Version => "1.3", 
    	Date => "May 30, 2013",
    	Authors => {
	     {Name => "Tom Enkosky", Email => "tenkosky@gmail.com"},
	     {Name => "Branden Stone", Email => "stonebranden@gmail.com", HomePage => "https://people.hamilton.edu/bstone/index.html"}	     	     
	     },
    	Headline => "AdmissibleFunctions",
    	DebuggingMode => true
    	)

export {
    
    -- Methods
     "hilbertFunList", 
     "macaulayRep",
     "sumRep",
     "hilbertRep",
     "isAdmissible",
     "hilbDiff",
     "isUnimodal",
     "isSymmetric",
     "isWLP",
     "wlpFunList",
     "LkList",
     "sumLkList",
     "bList"
--     "aListNum"
     
}


------------------------------------------------------------
-- METHODS
------------------------------------------------------------

--input: a non-negative integer A and non-negative integer D
--output: finds D^th Macaulay representation of A
--
macaulayRep = method()
macaulayRep(ZZ,ZZ) := (a,d) -> (
     local K; local L; local S; -- list variable
     
     --Special Cases. Will probably eleminate them later.
     if a==0 then (return  {{0,1}} );
     if d==1 then (return  {{a,1}} );
     if d == (a-1) then ( return {{a,d}} );
     if d>=a then (
	  return rsort pack(2, mingle((d-a+1)..d ,(d-a+1)..d ) );
	  );
     
     --Main algorithm.	 
     K = {};
     for j in ( rsort apply(d,i->i+1) ) 
     do (
	  for k in ( rsort apply(a,i->i) ) 
	  do (
	       S = sum apply( K, i-> binomial(i_0,i_1));
	       if S == a then break;
	       L = select( rsort apply( rsort apply( k, i->i+1), i->{i,j} ), i-> ( (a-S) >= binomial(i_0,i_1) )  );
	       if L == {} then continue;
	       K = append(K,first L);
	       break;
	       )
	  );
     return K;
     )


--input: a non-negative integer A and non-negative integer D
--output: the modified D^th Macaulay representatives A^<D>
--
hilbertRep = method()
hilbertRep(ZZ,ZZ) := (a,d) -> (
     return apply(macaulayRep(a,d), i -> apply(i, i -> i+1) );     
     )


--input: a list from hilbertRep or macaulayRep
--output: the sum of the representatives
--
sumRep = method()
sumRep(List) := L -> (
     return sum apply( L, i-> binomial(i_0,i_1));
     )

-- new mutable hashtable for hilbertFunList()
HilbertFunctions = new Type of MutableHashTable 

--input: an integer A that is the length of a module
--output: a hashtable of possible Hilbert Functions of length A.
--
hilbertFunList = method()
hilbertFunList(ZZ) := z -> (
     local H; local lastKey; local s;
         
     H = new HilbertFunctions;
     if z==1 then (H#0 = {1}; return H;);
     scan(z-1, i->( H#i = append({1},i+1) ) );

     scan( z-2, k -> ( 
	       scan( keys H, j -> (
			 if (#(H#j)>(k+1)) then ( 
			      lastKey = first rsort keys H;
			      s = sumRep hilbertRep((H#j)_(k+1),(k+1)); 
			      scan((lastKey+1)..(lastKey+s-1),i->( if ((sum H#j + i-lastKey+1)<=z) then ( H#i = append(H#j,i-lastKey+1) ) ) );
			      if ((sum H#j +1)<=z) then (H#j = append(H#j,1));
			      );
			 )
		    )
	       )
	  );
     return H;
     )

--#############################################################################
-- Methods for WLP
--#############################################################################


-- input: A list that represents a h-vector of an Artin algebra
-- output: The first difference of the h-vector
--
hilbDiff = method()
hilbDiff(List) := v -> ( 
     append ( prepend( 1, apply( #v-1, i -> v_(i+1)-v_i ) ), -last v )
     );

-- input: A list that represents a h-vector of an Artin algebra
-- output: Boolean volue saying whether or not the vector is an 
-- 	   admissible h-vector.
--     	 
isAdmissible = method()
isAdmissible(List) := v -> (
     local u; local T;
     
     T = (true, 0);
     u = append( v, 0 );
     
     scan( #v-1, i -> if( v_i < 0 ) then( T = (false, i); print"-- Input has negative values"; break;) );
     
     if ( T_0 == true )
     then (               
     scan(#v-1, i -> (
	  if( u_(i+2) > sumRep hilbertRep( u_(i+1), i+1 ) ) 
	  then (
	       T = (false, i+2);
	        break;
		); 
	   T = (true, 0); 
	   )
      );
      );
 
     return T_0;
);

-- input: A list that represents an h-vector of an artin algebra
-- output: A boolean value determining if list is unimodal
--
isUnimodal = method()
isUnimodal(List) := v -> (
     local L; local j; local T;
     
     T = false;
     j = 0;
     
     L = apply( hilbDiff v, i -> i > 0 );
     scan( #L-1, i -> if( L_i =!= L_(i+1) ) then( j = j+1 ) );
     
     if( j==1 ) then ( T = true );
     
     return ( j==1 );
     );

--input: An ordered list of integers
--output: A boolean value determining if the list is symmeteric or not
--
isSymmetric = method()
isSymmetric(List) := v -> (
     local n; local L;     

     n = #v-1;
     L = apply( floor(#v/2), i ->  v_i == v_(n-i) );

     return not member( false, L );
     );


--input: A list represtenting an h-vector of a Gorenstein algebra
--output: A boolean value determining whether the list has the Weak Leftshitz 
--     	  property. The criteria is taken from 
--
isWLP = method()
isWLP(List) := v -> (
     
 --    if not isSymmetric v then return false;
     
     if not isUnimodal v then return false;
     
     if not isAdmissible select( hilbDiff v, i -> i>0 ) then return false;
     
     return true;
     );

-- new mutatlbe hash table for wlpFunList()
WLPFunctions = new Type of MutableHashTable

-- input: A positive integer z representing the length of an artin algebra.
-- output: The hilbert functions of length z with WLP.
--     	   
wlpFunList = method()
wlpFunList(ZZ) := z ->(
    	local W; local L; local P;  
	
	L = values hilbertFunList z;
	P = delete( null, apply( L, l -> if isWLP l then l else null) );
	W = new WLPFunctions;
	scan( #P, i -> W#i = P#i );
    
    return W;      
)


--#############################################################################
-- Methods Building objects from Enkosky-Stone paper
--#############################################################################



-- input: (n,k) where n, k are positive integers
-- output: all possible h-vectors of length n of the form (1,k,...)
--
LkList = method()
LkList(ZZ,ZZ) := (n,k) -> (
     	  local L; local K; local K1;
	  
  	  L = hilbertFunList n;
     	  K = new MutableHashTable;
	  K1 = select( apply( values L, l -> if l_1 != k then {0} else l ), i -> i != {0} );
	  scan(#K1, i -> K#i = K1#i );

     return K;
     )


-- input: (n,k) where n, k are positive integers
-- output: all possible h-vectors of length n of the form (1,i,...) 
--     	   where i < k+1
--
sumLkList = method()
sumLkList(ZZ,ZZ) := (n,k) -> (
     	  local L; local K; local K1;

  	  L = hilbertFunList n;
     	  K = new MutableHashTable;
	  K1 = select( apply( values L, l -> if l_1 > k then {0} else l ), i -> i != {0} );
	  scan(#K1, i -> K#i = K1#i );

     return K;
     )


-- The set B
-- input: A positive integer z
-- output: The set B(z) as defined and constructed in Enkosky-Stone
--
bList = method()
bList(ZZ) := z -> (
     local H; local lastKey; local s;
         
     H = new HilbertFunctions;
     if z==1 then (H#0 = {1}; return H;);
     scan(z-1, i->( H#i = append({1},i+1) ) );

     scan( z-2, k -> ( 
	       scan( keys H, j -> (
			 if (#(H#j)>(k+1)) then ( 
			      lastKey = first rsort keys H;
			      s = sumRep hilbertRep((H#j)_(k+1),(k+1)); 
			      scan((lastKey+1)..(lastKey+s-1),i->( if ((sum H#j + i-lastKey+1)<=z) then ( H#i = append(H#j,i-lastKey+1) ) ) );
			      if ((sum H#j +1)<=z) then (H#j = append(H#j,1));
			      );
			 )
		    )
	       )
	  );
     return H;
     )









--------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------


beginDocumentation()

document {
     Key => AdmissibleFunctions,
     Headline => "A package to find admissible Hilbert Functions",
     
     "As is, this package determines the possible Hilbert Functions of a given length and all of the 
     necessary methods needed for the calculations.",
     
     PARA{}, "For the mathematical background see ",

     
     UL {
	  {"Winfried Bruns and Jürgen Herzog.", EM " Cohen-Macaulay Rings."},
	},
     
     }
 
document {
     Key => {hilbertFunList, (hilbertFunList, ZZ)},
     Headline => "Needs Checking",

}

document {
     Key => {macaulayRep, (macaulayRep,ZZ,ZZ)},
     Headline => "Calculates the d^th Macaulay representation of an integer a.",
     Usage => " C = macaulayRep(a,d)",
     Inputs => {
	  "a" => ZZ => {" an integer."},
	  "d" => ZZ => {" an integer."},	  
	  },
     Outputs => {
	  "C" => List => {" of piars of integers that represent the binomials in the ", TT "d^th", " Macaulay representation of ", TT "a", "."},
	  },
     
     PARA{}, "By the term Macaulay representation, we mean the unique binomial sum expansion of ", TT "a", " as defined on page 161 of Winfried Bruns and Jürgen Herzog, Cohen-Macaulay Rings.",

     EXAMPLE {
	  " C = macaulayRep(5,3)",
	  " B_0 = binomial toSequence C_0",
	  " B_1 = binomial toSequence C_1",	  
	  " 5 == B_0 + B_1",
	  },
     
}

document {
     Key => {sumRep, (sumRep,List)},
     Headline => "Needs Checking",

}

document {
     Key => {hilbertRep, (hilbertRep,ZZ,ZZ)},
     Headline => "Needs Checking",

}

document {
     Key => {isAdmissible, (isAdmissible,List)},
     Headline => "Needs Checking",

}

document {
     Key => {hilbDiff, (hilbDiff,List)},
     Headline => "Needs Checking",

}

document {
     Key => {isUnimodal, (isUnimodal,List)},
     Headline => "Needs Checking",

}

document {
     Key => {isSymmetric, (isSymmetric,List)},
     Headline => "Needs Checking",

}

document {
     Key => {isWLP, (isWLP,List)},
     Headline => "Needs Checking",

}

document {
     Key => {wlpFunList,(wlpFunList,ZZ)},
     Headline => "Needs Checking",

}

document {
     Key => {LkList,(LkList,ZZ,ZZ)},
     Headline => "Needs Checking",

}

document {
     Key => {sumLkList,(sumLkList,ZZ,ZZ)},
     Headline => "Needs Checking",

}

document {
     Key => {bList, (bList,ZZ)},
     Headline => "Needs Checking",

}

--document {
--     Key => {aListNum, (aListNum,ZZ)},
--     Headline => "Needs Checking",
--}


--------------------------------------------------
-- TESTS
--------------------------------------------------

-- Test 0
-- macaulayRep
TEST /// 
     assert( macaulayRep(3,5) == {{5,5},{4,4},{3,3}} );
     assert( macaulayRep(5,3) == {{4,3},{2,2}} );
///

-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------

end

-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------

restart
uninstallPackage "AdmissibleFunctions"
restart
installPackage "AdmissibleFunctions"
viewHelp AdmissibleFunctions

-- Tests
check(0, AdmissibleFunctions) -- macaulayRep
