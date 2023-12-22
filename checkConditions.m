/*************************************************
** MODULE NAME: checkConditions.m
** Author: Pedro-Jose Cazorla Garcia
** Affiliation: University of Manchester, UK.
** Description: This module includes functions that allow
**              to check sufficient conditions for asymptotic 
**              Fermat's Last Theorem to hold for the (p,p,2) 
**              Fermat type equation
**
**                Cx^2 + q^k*y^(2n) = z^n,
**
**              where z is assumed to be even. As shown in the paper,
**              only the parity of k is relevant in order to see 
**              whether AFLT holds.
**
**              In order to check the conditions, several auxiliary
**              Diophantine equations need to be solved.
**              
**              Some of the algorithms implemented here are based on 
**              the work of other researchers and are cited where 
**              appropiate.
**
**************************************************/

/*******************************************************************
***** Auxiliary functions - used to solve Mordell equations ********
*******************************************************************/

/******************************************************
** Name: solveMordellEquation
** Description: This function solves the Mordell equation
**                  y^2 = x^3 + a,
**              where x and y are S-integers, where S is 
**              a finite set of rational primes. The implementation here
**              is based upon Algorithm 4.2 in the paper 
**              
**              R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016
**              for values of p which are not too large and makes use of the 
**              in-built Magma function otherwise.
**
** Arguments: primes -> List of primes which are allowed to be in the denominator.
**            a -> Coefficient of the Mordell equation.
**
** Output: Solutions (x,y) of the Mordell equation which are S-integers.
******************************************************/
function solveMordellEquation(primes, a)

	solutions := {};
	
	/* We compute the bound aS in the paper */
	aS := 1728*(&*primes)^2;
	for p in PrimeDivisors(a) do
		if Valuation(a, p) eq 1 then
			aS *:= p;
		else
			aS *:= p^2;
		end if;
	end for;
	
	/* If this is too large, the computation via modular symbols IsEven
	   impractical and the elliptic curves are not in Cremona's database, 
	   so we compute them directly via S-integral points. */
	if aS ge 500000 then 
	
		/* The computation is often improved by precomputing generators. */
		E := EllipticCurve([0,0,0,0,a]);
		gens, found1, found2 := Generators(E);
		
		/* In this case, if the rank is 1, we could find a generator 
		   by looking for Heegner points. */
		if not found1 or not found2 then 
			min, max := RankBounds(E);
		
			if min eq 1 and max eq 1 then 
				found, P := HeegnerPoint(E);
			
				if found then 
					gens := [P];
				else
					print "Error in the computation";
					return -1;
				end if;
			end if;
		end if;
			
		pts := SIntegralPoints(E, primes : FBasis := gens);

		for point in pts do
			solutions := solutions join {[point[1], point[2]]};
		end for;
		
		return solutions;
	end if;
	
	/* Otherwise, all curves that we need are previously computed 
	   in Cremona's database, and we simply look them up */
	db := CremonaDatabase();
	
	for N in Divisors(aS) do
		nClasses := NumberOfIsogenyClasses(db, N);
		for i in [1..nClasses] do
			nCurves := NumberOfCurves(db, N, i);
			for j in [1..nCurves] do

				/* For every elliptic curve, we check if their invariants (c4, c6) 
				   satisfy the necessary conditions */
				E := EllipticCurve(db, N, i, j);
					
				invs := cInvariants(E);
				q := Abs((invs[1]^3- invs[2]^2)/a);
					
				m := Numerator(q);
				n := Denominator(q);
					
				mPower, u1 := IsPower(m, 12);
				nPower, u2 := IsPower(n, 12);
					
				if mPower and nPower then 
					u := u1/u2;
					x := invs[1]/u^4;
					y := invs[2]/u^6;
						
					if Set(PrimeDivisors(Denominator(x))) diff primes eq {} and Set(PrimeDivisors(Denominator(y))) diff primes eq {} then 
						solutions := solutions join {[x, y]};
					end if;
						
				end if;

			end for;
		end for;
	end for;

	return solutions;

end function;

/*******************************************************************
************************ Main functions ****************************
*******************************************************************/

/******************************************************
** Name: solveEquationPowerOf2
** Description: This function solves the main equation in the 
**              paper (the main obstruction, which needs to be 
**              computed in all cases). In other words, it finds 
**              all solutions (t, gamma, m) to 
**                 Ct^2 + q^gamma = 2^m,
**              only assuming that gamma, m > 0.
** 
**              If C, q are not too large, the Frey--Hellegouarch 
**              curve defined by Bennett-Skinner is in Cremona's
**              database, and we can simply look it up.
**
**              Otherwise, we reduce the problem to the resolution
**              of several Mordell equations.
**
** Arguments: C, q -> Coefficients of the equation, as above.
**
** Output: Solutions (t, gamma, m) of the equation, as above.
******************************************************/
function solveEquationPowerOf2(C, q)

	/* Sanity check on the arguments */
	assert IsPrime(q);
	assert IsOdd(C);
	assert IsOdd(q);
	assert (Gcd(C, q) eq 1);

	solutions := {};
	
	/* This is the conductor of the Frey--Hellegouarch curve. 
	   If this is not too large, solutions can be computed
	   directly by looking at Cremona's database.. */
	N := 2*C^2*q;

	if N le 500000 then 

		db := CremonaDatabase();
		nClasses := NumberOfIsogenyClasses(db, N);

		/* The Frey--Hellegouarch curve only recovers solutions with 
		   m >= 6. However, the rest can be found with an easy search */
		for n in [1..5] do
			for k in [1..Floor(n*Log(q, 2))] do
				x := Sqrt((2^n-q^k)/C);
				
				if IsIntegral(x) then
					solutions := solutions join {[Integers()!x, k, n]};
				end if;
			end for;
		end for;

		/* Here, we examine the minimal discriminant of the Frey--Hellegouarch curve
		   in order to recover the solutions */
		for i in [1..nClasses] do

			nCurves := NumberOfCurves(db, N, i);

			for j in [1..nCurves] do

				E := EllipticCurve(db, N, i, j);
				disc := Discriminant(MinimalModel(E));
				val := Valuation(disc, 2);

				n := (val+12)/2;
				k := Valuation(disc, q);
				x := (2^n-q^k)/C;
				x := Sqrt(x);

				if IsIntegral(n) and n ge 0 and IsIntegral(k) and k ge 0 and IsIntegral(x) then
					solutions := solutions join {[Integers()!x, Integers()!k, Integers()!n]};
				end if;

			end for;
		end for;
		
	/* In this case, the Frey--Hellegouarch curve is not on Cremona's database, so we need to 
	   compute S-integral points on curves. */
	else 
		/* Here, b is the congruence class of m modulo 3, while i is the 
		   congruence class of gamma modulo 6. It is sufficient to look 
		   for {q}-integral points on 15 elliptic curves. */
		for b in [0..2] do 
			for i in [0..5] do
				points := solveMordellEquation({q}, -4^b*C^3*q^i);
				
				/* This may have more points than we need, so we check whether the 
				   conditions are satisfied */
				for pt in points do
					u := pt[1];
					v := pt[2];
					
					valU := Valuation(u, q);
					valV := Valuation(v, q);
					
					if valU le 0 and (valU mod 2) eq 0 and valV le 0 and (valV mod 3) eq 0 and (valU div 2 eq valV div 3) then 
						
						/* The values of gamma and x can be recovered directly from the computed points */
						k := 3*Abs(valU) + i;
						x := v*q^Abs(valV)/(C^2*2^b);
						
						/* Since we want x to be an integer, we check if this is indeed the case. */
						if IsIntegral(x) then
							x := Integers()!x;
							pow, base, n := IsPower(C*x^2 + q^k);
							
							if pow and base eq 2 then 
								solutions := solutions join {[Abs(x), k, n]};
							end if;
						end if;
					
					end if;
				
				end for;
			end for;
		end for;
	end if;

	return solutions;

end function;


/******************************************************
** Name: solveRamanujanNagell
** Description: This function solves the Ramanujan–Nagell equation
**                  x^2 + b = cy,
**              where y is a S-unit, that is, a rational number supported
**              only on primes of a finite set S, and x is a S-integer.
**             
**              This is stronger than condition (c) in the theorem since 
**              the equation Cw^2 + 1 = q^gamma * 2^m can be written As
**                (Cw)^2 + C = C q^gamma * 2^m,
**              and it is therefore sufficient to solve this equation with 
**              b = c = C and S = {gamma,m}.
**              
**              The implementation here is based upon algorithm 6.1 in 
**              
**              R. von Kanel and B. Matschke, "Solving S-unit, Mordell, Thue, 
**              Thue–Mahler and Generalized Ramanujan–Nagell Equations via the 
**              Shimura–Taniyama Conjecture", Memoirs of the AMS, 2016
**
**              and makes use of the above function to solve Mordell equation.
**
** Arguments: b, c -> Coefficients of the above equation.
**            primes -> Finite list of primes where y is supported.
**
** Output: Solutions (x,y) on O x O^*, where O is the ring of S-integers.
******************************************************/
function solveRamanujanNagell(b, c, primes)

	solutions := {};
	
	/* The algorithm requires to solve several Mordell equations,
	   one for each divisor of the product of primes squared. */
	for e in Divisors((&*primes)^2) do 
	
		Ya := solveMordellEquation(primes, -b*(e*c)^2);
		
		/* For each solution of the Mordell equation, we reconstruct
		   the associated solution of the Ramanujan–Nagell equation */
		for solution in Ya do 
			u := solution[1];
			v := solution[2];
			
			x := v/(e*c);
			y := u^3/(e^2*c^3);
			
			if (x^2 + b) eq c*y then 
				solutions := solutions join {[Abs(x), y]};
			end if;
		
		end for;
	
	end for;
	
	return solutions;

end function;

/******************************************************
** Name: solvePowerEquation
** Description: This function checks condition (d) in the Theorem
**              by solving the Diophantine equation
**                 Cw^2 + 2^m = q^gamma,
**              only assuming that gamma, m > 0.
** 
**              This is done by reducing the computation to the 
**              resolution of some Mordell equations over rings
**              of S-integers. The implementation is similar to 
**              the second part of the function 
**              solveEquationPowerOf2 above.
**
** Arguments: C, q -> Coefficients of the equation, as above.
**
** Output: Solutions (w, m, gamma) of the equation, as above.
******************************************************/
function solvePowerEquation(C, q)

	solutions := {};
	
	/* Here, b is the congruence class of gamma modulo 3, while
	   i is the congruence class of m modulo 6. It is therefore
	   sufficient to solve 15 Mordell equations. */
	for b in [0..2] do 
		for i in [0..5] do
			points := solveMordellEquation({2}, -(q^2)^b*C^3*2^i);
				
				for pt in points do
					u := pt[1];
					v := pt[2];
					
					valU := Valuation(u, 2);
					valV := Valuation(v, 2);
					
					/* There may be more points than we need, so we check if all conditions are satisfied and, in 
					   the affirmative case, we add the solutions. */
					if valU le 0 and (valU mod 2) eq 0 and valV le 0 and (valV mod 3) eq 0 and (valU div 2 eq valV div 3) then 
						k := 3*Abs(valU) + i;
						x := v*2^Abs(valV)/(C^2*q^b);
						
						if IsIntegral(x) then
							x := Integers()!x;
							pow, base, n := IsPower(C*x^2 + 2^k);
							
							if pow and base eq q then 
								solutions := solutions join {[Abs(x), k, n]};
							end if;
						end if;
					
					end if;
				
				end for;
			end for;
	end for;

	return solutions;


end function;

/******************************************************
** Name: checkAFLT
** Description: This function uses the previous three functions
**              to confirm the conditions in the Theorem. If all
**              are satisfied, it returns true and AFLT is verified
**              for the values of C, q and k specified in the equation
**
**                Cx^2 + q^k*y^(2n) = z^n,
**              where z is assumed to be even.
**
**              Note that the actual value of k is irrelevant, and 
**              only its parity is relevant for this function.
**
** Arguments: C, q -> Coefficients of the equation, as above.
**
** Output: True if all conditions in the theorem are verified, and, therefore
**              AFLT is true for the family of equations.
**         False if AFLT could not be verified.
******************************************************/
function checkAFLT(C, q, k)

	assert IsPrime(q) or q eq 1;
	assert IsOdd(C);
	assert IsOdd(q);
	assert Gcd(C, q) eq 1;
	
	/* We check the first condition in the theorem. This needs 
       to be checked for all values of C, q and k.	*/
	sols := solveEquationPowerOf2(C, q);
	
	for sol in sols do
		x1 := sol[1];
		k1 := sol[2];
		n1 := sol[3];
		
		/* Solutions should have k with the same parity as our desired k
		   and n > 6 */
		if IsEven(k-k1) and n1 gt 6 then
			return false;
		end if;
		
	end for;
	
	/* If k is even and -C is a square modulo q, there 
	   are more conditions to check */
	   
	if IsEven(k) and LegendreSymbol(-C, q) eq 1 then 
	
		/* Condition (c) in the theorem */
		sols := solveRamanujanNagell(C, C, {q,2});
		
		for sol in sols do 
			x1 := sol[1]/C;
			m1 := Valuation(sol[2], q);
			m2 := Valuation(sol[2], 2);
			
			if IsIntegral(x1) and m1 gt 0 and m2 gt 6 then  
				return false;
			end if;
		end for;
	
		/* If q = 7 (mod 8), it is possible for condition (d)
		   to hold, so we need to check it */
		if (q mod 8) eq 7 then 
			sols := solvePowerEquation(C, q);
			
			for sol in sols do
				x1 := sol[1];
				k1 := sol[2];
				m1 := sol[3];
				
				if k1 gt 6 and IsEven(k1) and m1 gt 0 and IsOdd(m1) then 
					return false;
				end if;
			end for; 
		end if;
	end if;

	/* If all tests have been passed, we return true. */
	return true;
	
end function;

/******************************************
** SANITY CHECK ***************************
******************************************/

/*
for C in [y: y in [1..20] | IsSquarefree(y)] do
	for q in [x : x in [3..25] | IsPrime(x)] do
		
		if (C*q mod 8) eq 7 and Gcd(C, q) eq 1 then 
			print "C=", C, ", q=", q, "k odd, success=", checkAFLT(C, q, 1);
		end if;
		
		if (C mod 8) eq 7 and Gcd(C, q) eq 1 then 
			print "C=", C, ", q=", q, "k even, success=", checkAFLT(C, q, 2);
		end if;
	end for;
end for;
*/