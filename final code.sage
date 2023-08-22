import time
from sage.databases.cremona import parse_cremona_label
import numpy as numpy

#this is the final code used for the computation

def iwasawa_invariants_of_ec(E,p,D = 1):
	"""
	Returns the mu and lambda invariants, and the valuations of the roots of the +/- p-adic L-function of E.  
	If the minimal mu-invariant fails to be 0, then '?' is returned for mu
	Input:
	-``E`` -- elliptic curve
	-``p`` -- prime, this code works only for odd primes
  	- ``D`` -- The discriminant of the quadratic field being twisted by, 1 by default, eg if the field is Q(\sqrt(-23)), then D = -23, if 
	-	   it is Q(\sqrt(-21)), then enter D = -84
  	Output:
	In the supersingular case: (mu_plus,mu_minus), [lambda_plus, valuations of roots of Lp+,lambda_minus, valuations of roots of Lp-]
	If the constant terms of L_p^+, L_p^- are non-vanishing then the valuations of the roots obtained are exact, as proven in the article
	However, if the constant term vanishes, then the valuations of the roots returned might not be exact, and further approximations
	   may need to be computed to obtain the exact valuations.
	In the examples presented in the article, the constant term is always non-zero and hence the valuation obtained are exact.
	Note that the forced zero at 0 due to the functional equation does not show up in list of valuations of roots
	If the minimal mu wasn't found to be, then mu's are returned as '?'
	"""
	Etwist = E.quadratic_twist(D)
	if Etwist.is_supersingular(p): #checks if E is supersingular at p
		r = Etwist.analytic_rank()
		correction = 0 
		if (E.quadratic_twist(D)).root_number() == -1:
			correction = 1 # This accounts for the forced zero at T = 0 due to the functional equation
		MTs = [MazurTate(E,p,1,D), MazurTate(E,p,2,D)] # Keeps track of Mazur-Tate elements
		done = (mu(MTs[0],p) == 0) and (mu(MTs[1],p) == 0)
		n = 3
		while not done and (n <= mu_bail(p)): #Computes the level at which the mu invariant vanishes for L_{p,n}^{+-}
			MTs += [MazurTate(E,p,n,D)] 
			done = (mu(MTs[n-1],p) == 0) and (mu(MTs[n-2],p) == 0)
			n = n + 1
		if done == 0:
			print("mu-invariant does not vanish")
		n = n - 1
		Qp = pAdicField(p,2*n+5)
		S.<T> = PolynomialRing(Qp)
		R.<T> = PolynomialRing(QQ)
		def approx(poly,m):   
      		#This function computes approximations to Lp +/- and computes their newton slopes
			if m%2 == 1:
				quotient = (poly.factor()/Phip(m,p)).expand()
				return R(quotient)
			if m%2 == 0:
				quotient = (poly.factor()/Phim(m,p)).expand()
				return R(quotient)
		def lambdamw(quotient): #This computes the lambda_III
			R.<T> = PolynomialRing(QQ) ; quotient = R(quotient)                
			l = []
			for j in range(1,lamb(quotient,p)+1):
				if cyc(j,p).divides(quotient):
					l += (S(cyc(j,p))).newton_slopes()
			return l
		#The next piece of code computes the lambda invariants, I use the last two mazur tate elements computed
		if n%2 == 0:        
			lambda_plus = lamb(MTs[n-2],p)-qn(p,n-1) 
			lambda_minus = lamb(MTs[n-1],p)-qn(p,n) 
			if correction == 1 and lambda_plus == 1 and lambda_minus == 1:
				return (0,0),[0,1,[],0,1,[]]
			Lpplus = (-1)^(n/2)*approx(MTs[n-2],n-1) 
			Lpminus = (-1)^(n/2)*approx(MTs[n-1],n)
			k = needed(p,lambda_plus, lambda_minus)
			if Lpplus[0]!= 0 and Lpminus[0] != 0: #checks if constant term is non-zero, if it is, then we compute approximations to the required level     
				Nplus = k[0] + 2*Lpplus[0].valuation(p)
				Nminus = k[1] + 2*Lpminus[0].valuation(p)
				enough = n >= Nplus and n >= Nminus 
				while not enough:             
					n = n + 1
					if n%2 == 0 and n < Nminus + 1:
						Lpminus = approx(MazurTate(E,p,n,D),n)
					elif n%2 == 1 and n < Nplus + 1:
						Lpplus = approx(MazurTate(E,p,n,D),n)
					Nplus = k[0] + 2*Lpplus[0].valuation(p)
					Nminus = k[1] + 2*Lpminus[0].valuation(p)
					enough = n >= Nplus and n >= Nminus
			slopes_plus = [i for i in S(Lpplus).newton_slopes() if i > 0]
			lambdamw_plus = len(lambdamw(Lpplus)) + correction
			lambdaIII_plus = lambda_plus - lambdamw_plus 
			slopes_minus = [i for i in S(Lpminus).newton_slopes() if i > 0] 
			lambdamw_minus = len(lambdamw(Lpminus)) + correction
			lambdaIII_minus = lambda_minus - lambdamw_minus 
		else:
			lambda_minus = lamb(MTs[n-2],p)-qn(p,n-1) 
			lambda_plus = lamb(MTs[n-1],p)-qn(p,n)
			if correction == 1 and lambda_plus == 1 and lambda_minus == 1:
				return (0,0),[0,1,[],0,1,[]]
			Lpplus = (-1)^((n+1)/2)*approx(MTs[n-1],n) 
			Lpminus = (-1)^((n+1)/2)*approx(MTs[n-2],n-1)
			k = needed(p,lambda_plus, lambda_minus)
			if Lpplus[0] != 0 and Lpminus[0] != 0: #checks if constant term is non-zero, if it is, then we compute approximations to the required level
				Nplus = k[0] + 2*Lpplus[0].valuation(p)
				Nminus = k[1] + 2*Lpminus[0].valuation(p)        
				enough = n >= Nplus and n >= Nminus 
				while not enough and Lpplus[0] !=0 and Lpminus[0] != 0:             
					n = n + 1
					if n%2 == 0 and n < Nminus + 1:
						Lpminus = approx(MazurTate(E,p,n,D),n)
					elif n%2 == 1 and n < Nplus + 1:
						Lpplus = approx(MazurTate(E,p,n,D),n)
					Nplus = k[0] + 2*Lpplus[0].valuation(p)
					Nminus = k[1] + 2*Lpminus[0].valuation(p)
					enough = n >= Nplus and n >= Nminus
			slopes_plus = [i for i in S(Lpplus).newton_slopes() if i > 0]
			lambdamw_plus = len(lambdamw(Lpplus)) + correction
			lambdaIII_plus = lambda_plus - lambdamw_plus
			slopes_minus = [i for i in S(Lpminus).newton_slopes() if i > 0]            
			lambdamw_minus = len(lambdamw(Lpminus)) + correction
			lambdaIII_minus = lambda_minus - lambdamw_minus
		return (0,0), [lambda_plus, slopes_plus,lambda_minus, slopes_minus]
	else : raise ValueError('the elliptic curve(or its twist if D != 1) is not supersingular at the prime p')

def MazurTate(E,p,n,D = 1):
	"""
	Returns the p-adic Mazur-Tate element of level n.  That is, for p odd, we take the element
		sum_{a in (Z/p^{n+1}Z)^*} [a/p^{n+1}]^+_E sigma_a
	in Q[Gal(Q(mu_{p^{n+1}}))] and project it to Q[Gal(Q_n/Q)] where Q_n is the
	n-th level of the cyclotomic Z_p-extension.  The projection here is twisted by omega^twist so 
	that the group algebra element [a] maps to omega^twist(a)[a].
	(For p=2, one projects from level n+2, see Kurihara-Otsuki)
	Input:
	-	``E`` -- elliptic curve
	-	``p`` -- prime
	-	``n`` -- integer >= -1
	-	``phi`` -- None (default) or an order pair where phi[0] is the modular symbol attached
		to an elliptic curve in the isogeny class of E (typically chosen to minimize the mu-invariant
		in the isogeny class) and phi[1] is a constant used to rescale phi[0] (typically chosen to be
		1/(# of real components of E).  This ordered pair business can be dropped once SAGE's 
		normalization problems with modular symbols is fixed
	"""
	start = time.time()
	if D > 0:
		M1 = E.modular_symbol()
	else:
		M1 = E.modular_symbol(sign = -1)
	def twisted_modularsymbol(r):
		answer = 0
		for a in Zmod(abs(D)).list_of_elements_of_multiplicative_group():
			answer = answer + kronecker(D,a)*M1(r+a/abs(D))
		return answer
	R.<T> = PolynomialRing(QQ)    
	if n > 0:
		mt = R(0)
		if p > 2:
			gam = 1+p
			## should check carefully the accuracy needed here
			Qp = pAdicField(p,2*n+5)
			teich = Qp.teichmuller_system()
			teich = [0] + teich  ## makes teich[a] = omega(a)
			teich = [ZZ(teich[a]) for a in range(p)]
			gampow = 1 ## will make gampow = gam^pow
			oneplusTpow = 1 ## will make oneplusTpow = (1+T)^pow
			for j in range(p^(n)):
				cj = sum([twisted_modularsymbol(gampow * teich[a] / p^(n+1)) for a in range(1,(p+1)/2)])
				mt = mt + R(cj) * oneplusTpow
				gampow = gampow * gam
				oneplusTpow = oneplusTpow * (1 + T)
			end = time.time()
			t = end-start
			ans = 2*mt
	return ans

def mu(f,p):
	"""Returns the (p-adic) mu-invariant of f"""
	if f == 0:
		return oo
	else:
		return min([f[a].valuation(p) for a in range(f.degree()+1)])

def lamb(f,p):
	"""Returns the (p-adic) lambda-invariant of f"""
	if f == 0:
		return oo
	else:
		m = mu(f,p)
		v = [f[a].valuation(p) for a in range(f.degree()+1)]
		return v.index(m)

def qn(p,n):
	""""q_n as defined by Kurihara"""
	if n%2 == 0:
		return sum([p^a - p^(a-1) for a in range(1,n,2)])
	else:
		return sum([p^a - p^(a-1) for a in range(2,n,2)])

def cyc(n, p):
    #This is new (not from Pollack's code)
    #creates the cyclotomic polynomial Phi_n(poly)
    R.<T> = PolynomialRing(QQ)
    ans = R(0)
    for j in range(p):
        ans = ans + (1+T)^(p^(n-1)*j)
    return ans

def Phip(n,p):
    #This is new (not from Pollack's code)
    #computes the product of phi_j(poly) for even j less than or equal to n
    R.<T> = PolynomialRing(QQ)
    ans = R(1)
    for j in [2*i for i in range(1,integer_floor((n+2)/2))]:
        ans = ans * cyc(j, p)
    return ans

def Phim(index,p):
    #This is new (not from Pollack's code)
    #computes the product of phi_j(poly), for odd j less than or equal to n
    R.<T> = PolynomialRing(QQ)
    ans = R(1)
    for j in [2*i - 1 for i in range(1,integer_floor((index+3)/2))]:
        ans = ans * cyc(j, p)
    return ans

def mu_bail(p):
	"""
	For a given prime p, returns the n for which we should keep trying to 
	compute Mazur-Tate elements to level p^n in hoping that their mu-invariants will vanish.
	The below values were just picked after a few trial runs.  In practice,
	mu should always eventually be zero (by how the code is normalized) and
	so these parameters are just setting how long we want to wait
	Input:
	-	``p`` -- prime
	"""
	if p<1000:
		return max(round(log(1000)/log(p)),4)-1
	else:
		return -1

def needed(p,d1,d2):
    done = 0
    n = 1
    check1 = (p^(n+1) - 1)/(p+1) > d1
    while check1 == 0:
        n = n + 2
        check1 = (p^(n+1) - 1)/(p+1) > d1
    l = [n]
    n = 2
    check2 = p*(p^n - 1)/(p+1) > d2
    while check2 == 0:
        n = n + 2
        check2 = p*(p^n - 1)/(p+1) > d2
    l.append(n)
    return l
