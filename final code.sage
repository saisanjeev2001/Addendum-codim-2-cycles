import time
from sage.databases.cremona import parse_cremona_label
import numpy as numpy

#this is the final code, modified so as to compute modular symbol only once, also includes paramter for level of Mazur tate

def iwasawa_invariants_of_ec(E,p,D = 1,m = 0):
	"""
	Returns the mu and lambda invariants of E (for the prime p).  
	If the minimal mu-invariant fails to be 0, then '?' is returned for mu
	Input:
	-	``E`` -- elliptic curve
	-	``p`` -- prime, this code works only for odd primes
  - ``D`` -- The discriminant of the quadratic field being twisted by, 1 by default
  - ``m`` -- The additional depth to which we wish to compute the slopes, to get a better estimate of the final slopes, 0 by default
  Output:
	In the supersingular case: 
	If the minimal mu wasn't found to be, then mu's are returned as '?'
	"""
	if E.is_supersingular(p): #checks if E is supersingular at p
 		correction = 0 
		if (E.quadratic_twist(D)).root_number() == -1:
			correction = 1 # This accounts for the forced zero at T = 0 due to the functional equation
		MTs = [MazurTate(E,p,1,M1,D), MazurTate(E,p,2,M1,D)] # Keeps track of Mazur-Tate elements
		done = (mu(MTs[0],p) == 0) and (mu(MTs[1],p) == 0)
		n = 3
		while not done and (n <= mu_bail(p)): #Computes the level at which the mu invariant vanishes for L_{p,n}^{+-}
			MTs += [MazurTate(E,p,n,M1,D)] 
			done = (mu(MTs[n-1],p) == 0) and (mu(MTs[n-2],p) == 0)
			n = n + 1
		for i in range(m): #This computes few more levels to get the desired accuracy of valuation of roots
			MTs += [MazurTate(E,p,n+i,M1,D)]
		n = n + m - 1
		Qp = pAdicField(p,2*n+5)
		S.<T> = PolynomialRing(Qp)
		def slopes(poly,m):   
      #This function computes approximations to Lp +/- and computes their newton slopes
			if m%2 == 1:
				quotient = (poly.factor()/Phip(m,p)).expand()                
				Lpplus = S(quotient)
				return [Lpplus.newton_slopes(),quotient]
			if m%2 == 0:
				quotient = (poly.factor()/Phim(m,p)).expand()
				Lpminus = S(quotient)
				return [Lpminus.newton_slopes(),quotient]
		def lambdamw(quotient): #This computes the lambda_III
			R.<T> = PolynomialRing(QQ) ; quotient = R(quotient)                
			l = []
			for j in range(1,lamb(quotient,p)+1):
				if cyc(j,p).divides(quotient):
					l += (S(cyc(j,p))).newton_slopes()
			return l
		#The next piece of code computes the lambda invariants, I use the last two mazur tate elements computed
		if n%2 == 0:                
			mu_plus = mu(MTs[n-2],p) 
			lambda_plus = lamb(MTs[n-2],p)-qn(p,n-1) 
			lambda_minus = lamb(MTs[n-1],p)-qn(p,n) 
			if correction == 1 and lambda_plus == 1 and lambda_minus == 1:
				return (0,0),[0,1,[],0,1,[]]
			lambdamw_plus = len(lambdamw(slopes(MTs[n-2],n-1)[1])) + correction
			lambdaIII_plus = lambda_plus - lambdamw_plus 
			mu_minus = mu(MTs[n-1],p)
			slopes_minus = [i for i in (slopes(MTs[n-1],n))[0] if i > 0] ; slopes_plus = [i for i in slopes(MTs[n-2],n-1)[0] if i > 0]
			lambdamw_minus = len(lambdamw(slopes(MTs[n-1],n)[1])) + correction
			lambdaIII_minus = lambda_minus - lambdamw_minus
		else:
			mu_minus = mu(MTs[n-2],p)
			lambda_minus = lamb(MTs[n-2],p)-qn(p,n-1) 
			lambda_plus = lamb(MTs[n-1],p)-qn(p,n)
			if correction == 1 and lambda_plus == 1 and lambda_minus == 1:
				return (0,0),[0,1,[],0,1,[]]
			lambdamw_minus = len(lambdamw(slopes(MTs[n-2],n-1)[1])) + correction
			lambdaIII_minus = lambda_minus - lambdamw_minus
			mu_plus = mu(MTs[n-1],p)
			slopes_minus = [i for i in slopes(MTs[n-2],n-1)[0] if i > 0] ; slopes_plus = [i for i in (slopes(MTs[n-1],n))[0] if i > 0]
			lambdamw_plus = len(lambdamw(slopes(MTs[n-1],n)[1])) + correction
			lambdaIII_plus = lambda_plus - lambdamw_plus
		if mu_plus != 0:
			line='For '+E.label()+' and p='+str(p)+' mu+ is '+str(mu_plus)
			warnings.warn(line)
			mu_plus = '?'
		if mu_minus != 0:
			line='For '+E.label()+' and p='+str(p)+' mu- is '+str(mu_minus)
			warnings.warn(line)
			mu_minus = '?'
		if mu_plus == '?' or mu_minus == '?':
			return '?',(lambda_plus,lambda_minus)
		else:
			return (mu_plus,mu_minus), [lambda_plus, slopes_plus,lambda_minus, slopes_minus]

def MazurTate(E,p,n,M1,D = 1):
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
	if modp and (p!=2):
		R.<T> = PolynomialRing(QQ)
	else:
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
			if t>=bigcall:
				line = E.label()+": p="+str(p)+", n="+str(n)
				line += ", time: "+str(end-start)+"\n"
				write_to_file(bigcallfile,line)
      ans = 2*R(mt)
				##extra factor of 2 here is because we are only summing up to (p-1)/2
				##and using the + modular symbol
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
