restart:
interface(prettyprint = 0):
kernelopts(printbytes = false):

with(LinearAlgebra):

# ----------------------------------------------------------------------
# Parameters
# ----------------------------------------------------------------------
alpha := 3:
alphaInv := 159:                    # 3*159 = 1 mod 238
p := 239:
DFiber := 17:                         # do not use name D: Maple protects D as differentiation
R := 3:

InvBranches := [0, 2]:
KnownBranch := 0:
hprev := 0:

NUM_FIBERS := 20:
PRINT_SOLUTIONS := false:

if igcd(alpha, p - 1) <> 1 then
    error "gcd(alpha,p-1) != 1"
end if:

if irem(p - 1, DFiber) <> 0 then
    error "D does not divide p-1"
end if:

if irem(alpha * alphaInv, p - 1) <> 1 then
    error "alphaInv is incorrect"
end if:

# ----------------------------------------------------------------------
# Modular helpers
# ----------------------------------------------------------------------
FpRed := proc(e)
    return Expand(e) mod p
end proc:

PowFp := proc(a, e)
    return (a &^ e) mod p
end proc:

NumMon := proc(e)
    local ee:
    ee := Expand(e) mod p:

    if ee = 0 then
        return 0
    elif type(ee, `+`) then
        return nops(ee)
    else
        return 1
    end if
end proc:

# ----------------------------------------------------------------------
# MDS matrix and fixed round constants
# ----------------------------------------------------------------------
M := Matrix([[45,  21, 171],
             [21, 171,  43],
             [171, 43,  32]]):

if Determinant(M) mod p = 0 then
    error "M is singular modulo p"
end if:

C := Array(0 .. 9):
C[0] := [ 70, 185,   7]:
C[1] := [229,  46, 100]:
C[2] := [ 88,  19, 209]:
C[3] := [165,  11, 129]:
C[4] := [ 69,  52, 138]:
C[5] := [ 19,  44, 223]:
C[6] := [193,  62,  64]:
C[7] := [ 35,  95,  19]:
C[8] := [  9, 111,  78]:
C[9] := [ 42,  71, 162]:

# A cubic over a field is irreducible iff it has no field root.
for aa from 0 to p - 1 do
    if FpRed(aa^3 + aa^2 + aa + 5) = 0 then
        error "T^3+T^2+T+5 is reducible over F_p"
    end if
end do:

# ----------------------------------------------------------------------
# Vector operations
# ----------------------------------------------------------------------
AddC := proc(v, cvec)
    local i:
    return [seq(FpRed(v[i] + cvec[i]), i = 1 .. 3)]
end proc:

LinM := proc(v)
    local i, j:
    return [seq(FpRed(add(M[i, j] * v[j], j = 1 .. 3)),
                i = 1 .. 3)]
end proc:

AffineBefore := proc(v, cvec)
    return LinM(AddC(v, cvec))
end proc:

AffineAfter := proc(v, cvec)
    return AddC(LinM(v), cvec)
end proc:

SAlphaVec := proc(v)
    local i:
    return [seq(FpRed(v[i]^alpha), i = 1 .. 3)]
end proc:

# ----------------------------------------------------------------------
# P3 step for alpha=3 over
# F_p[T]/(T^3+T^2+T+5), so T^3=-T^2-T-5.
# ----------------------------------------------------------------------
Pi2 := proc(v)
    local a, b, d, y0, y1, y2:

    a := v[1]:
    b := v[2]:
    d := v[3]:

    y0 := a^3
        - 5*b^3
        + 20*d^3
        + 15*a*d^2
        + 15*b^2*d
        - 30*a*b*d:

    y1 := 3*a^2*b
        - b^3
        + 4*d^3
        - 12*a*d^2
        - 12*b^2*d
        + 15*b*d^2
        - 6*a*b*d:

    y2 := 3*a^2*d
        + 3*a*b^2
        - b^3
        + 9*d^3
        - 12*b*d^2
        - 6*a*b*d:

    return [FpRed(y0), FpRed(y1), FpRed(y2)]
end proc:

# ----------------------------------------------------------------------
# Numeric permutation, used only for brute-force ground truth and final
# verification.
# ----------------------------------------------------------------------
ApplyInvBranches := proc(v)
    local w, br, idx:

    w := v:

    for br in InvBranches do
        idx := br + 1:
        w := subsop(idx = PowFp(v[idx], alphaInv), w):
    end do:

    return w
end proc:

Permute := proc(v)
    local state, pre, r:

    state := v:

    for r from 1 to R do
        state := AffineBefore(state, C[3*r - 3]):
        state := SAlphaVec(state):

        pre := AffineAfter(state, C[3*r - 2]):
        state := ApplyInvBranches(pre):

        state := AddC(state, C[3*r - 1]):
        state := Pi2(state):
    end do:

    return AffineAfter(state, C[9])
end proc:

# ----------------------------------------------------------------------
# Fiber and triangular reduction.
# ----------------------------------------------------------------------
FiberReduce := proc(e, c1, c2)
    local res:

    res := FpRed(e):

    if res = 0 then
        return 0
    end if:

    res := Rem(res, x1^DFiber - c1, x1) mod p:
    res := Rem(res, x2^DFiber - c2, x2) mod p:

    return FpRed(res)
end proc:

ReduceAll := proc(e, eq_list, c1, c2)
    local res, j, zvar, A:

    res := FiberReduce(e, c1, c2):

    if nops(eq_list) = 0 or res = 0 then
        return res
    end if:

    for j from nops(eq_list) by -1 to 1 do
        zvar := eq_list[j][1]:
        A    := eq_list[j][2]:

        res := Rem(res, zvar^alpha - A, zvar) mod p:
        res := FiberReduce(res, c1, c2):
    end do:

    return res
end proc:

ReduceState := proc(state, eq_list, c1, c2)
    local i:
    return [seq(ReduceAll(state[i], eq_list, c1, c2), i = 1 .. 3)]
end proc:

# ----------------------------------------------------------------------
# Reduced arithmetic.
# ----------------------------------------------------------------------
MulRed := proc(u, v, eq_list, c1, c2)
    return ReduceAll(FpRed(u * v), eq_list, c1, c2)
end proc:

TermRed := proc(c, L, eq_list, c1, c2)
    local res, k:

    res := FpRed(c):

    for k from 1 to nops(L) do
        res := MulRed(res, L[k], eq_list, c1, c2):
    end do:

    return res
end proc:

SumRed := proc(L, eq_list, c1, c2)
    local s, k:

    s := 0:

    for k from 1 to nops(L) do
        s := ReduceAll(FpRed(s + L[k]), eq_list, c1, c2):
    end do:

    return s
end proc:

Pow3Red := proc(u, eq_list, c1, c2)
    local u2, u3:

    u2 := MulRed(u, u, eq_list, c1, c2):
    u3 := MulRed(u2, u, eq_list, c1, c2):

    return u3
end proc:

SAlphaVecRed := proc(v, eq_list, c1, c2)
    local i:
    return [seq(Pow3Red(v[i], eq_list, c1, c2), i = 1 .. 3)]
end proc:

Pi2Red := proc(v, eq_list, c1, c2)
    local a, b, d, y0, y1, y2:

    a := v[1]:
    b := v[2]:
    d := v[3]:

    y0 := SumRed([
        TermRed(  1, [a, a, a], eq_list, c1, c2),
        TermRed( -5, [b, b, b], eq_list, c1, c2),
        TermRed( 20, [d, d, d], eq_list, c1, c2),
        TermRed( 15, [a, d, d], eq_list, c1, c2),
        TermRed( 15, [b, b, d], eq_list, c1, c2),
        TermRed(-30, [a, b, d], eq_list, c1, c2)
    ], eq_list, c1, c2):

    y1 := SumRed([
        TermRed(  3, [a, a, b], eq_list, c1, c2),
        TermRed( -1, [b, b, b], eq_list, c1, c2),
        TermRed(  4, [d, d, d], eq_list, c1, c2),
        TermRed(-12, [a, d, d], eq_list, c1, c2),
        TermRed(-12, [b, b, d], eq_list, c1, c2),
        TermRed( 15, [b, d, d], eq_list, c1, c2),
        TermRed( -6, [a, b, d], eq_list, c1, c2)
    ], eq_list, c1, c2):

    y2 := SumRed([
        TermRed(  3, [a, a, d], eq_list, c1, c2),
        TermRed(  3, [a, b, b], eq_list, c1, c2),
        TermRed( -1, [b, b, b], eq_list, c1, c2),
        TermRed(  9, [d, d, d], eq_list, c1, c2),
        TermRed(-12, [b, d, d], eq_list, c1, c2),
        TermRed( -6, [a, b, d], eq_list, c1, c2)
    ], eq_list, c1, c2):

    return [y0, y1, y2]
end proc:

PrefixEqs := proc(L, n)
    local k:

    if n <= 0 then
        return []
    end if:

    return [seq(L[k], k = 1 .. n)]
end proc:

# ----------------------------------------------------------------------
# Cubic norm for auxiliary elimination.
# ----------------------------------------------------------------------
CubicNormRed := proc(f, A, z, prev_eqs, c1, c2)
    local ff, AA, dz, a0, a1, a2, t0, t1, t2, t3:

    ff := ReduceAll(f, prev_eqs, c1, c2):

    if ff = 0 then
        return 0
    end if:

    ff := collect(ff, z):
    dz := degree(ff, z):

    if dz > 2 then
        error "degree in %1 is %2, expected <= 2", z, dz
    end if:

    AA := ReduceAll(A, prev_eqs, c1, c2):

    a0 := ReduceAll(coeff(ff, z, 0), prev_eqs, c1, c2):
    a1 := ReduceAll(coeff(ff, z, 1), prev_eqs, c1, c2):
    a2 := ReduceAll(coeff(ff, z, 2), prev_eqs, c1, c2):

    t0 := Pow3Red(a0, prev_eqs, c1, c2):
    t1 := TermRed( 1, [AA, Pow3Red(a1, prev_eqs, c1, c2)],
                   prev_eqs, c1, c2):
    t2 := TermRed( 1, [AA, AA, Pow3Red(a2, prev_eqs, c1, c2)],
                   prev_eqs, c1, c2):
    t3 := TermRed(-3, [AA, a0, a1, a2],
                   prev_eqs, c1, c2):

    return SumRed([t0, t1, t2, t3], prev_eqs, c1, c2)
end proc:

# ----------------------------------------------------------------------
# Build the system on one fixed fiber and eliminate z6,...,z1.
#
# Input state: [x1,x2,0].
# Two inverse branches per round give six auxiliary variables.
# ----------------------------------------------------------------------
BuildAndEliminateFiber := proc(c1, c2)
    local state, eq_list, z_list, A_list, aux_idx,
          r, pre, state_after_B, br, idx, zvar,
          out, fh, i, prev_eqs, t0, buildTime, elimTime:

    state := [x1, x2, 0]:
    eq_list := []:
    z_list := []:
    A_list := []:
    aux_idx := 0:

    t0 := time():

    for r from 1 to R do
        # F
        state := AffineBefore(state, C[3*r - 3]):
        state := SAlphaVecRed(state, eq_list, c1, c2):
        state := ReduceState(state, eq_list, c1, c2):

        # B' affine part
        pre := AffineAfter(state, C[3*r - 2]):
        pre := ReduceState(pre, eq_list, c1, c2):
        state_after_B := pre:

        # Introduce inverse-power outputs z_i with z_i^3=pre_i.
        for br in InvBranches do
            idx := br + 1:
            aux_idx := aux_idx + 1:
            zvar := parse(cat("z", aux_idx)):

            A_list := [op(A_list), pre[idx]]:
            z_list := [op(z_list), zvar]:
            eq_list := [op(eq_list), [zvar, pre[idx]]]:

            state_after_B := subsop(idx = zvar, state_after_B):
        end do:

        # P3
        state := AddC(state_after_B, C[3*r - 1]):
        state := Pi2Red(state, eq_list, c1, c2):
        state := ReduceState(state, eq_list, c1, c2):
    end do:

    out := AffineAfter(state, C[9]):
    fh := ReduceAll(FpRed(out[KnownBranch + 1] - hprev),
                    eq_list, c1, c2):

    buildTime := time() - t0:

    # Reverse auxiliary elimination.
    t0 := time():

    for i from nops(z_list) by -1 to 1 do
        prev_eqs := PrefixEqs(eq_list, i - 1):

        fh := CubicNormRed(fh, A_list[i], z_list[i],
                           prev_eqs, c1, c2):
        fh := ReduceAll(fh, prev_eqs, c1, c2):

        gc():
    end do:

    elimTime := time() - t0:

    # fh is now a polynomial in x1,x2, reduced modulo both fiber relations.
    return [fh, buildTime, elimTime]
end proc:

# ----------------------------------------------------------------------
# Roots of x^D=c in F_p.
# ----------------------------------------------------------------------
FiberRoots := proc(c)
    local roots, a:

    roots := []:

    for a from 1 to p - 1 do
        if PowFp(a, DFiber) = c then
            roots := [op(roots), a]:
        end if:
    end do:

    return roots
end proc:

# ----------------------------------------------------------------------
# Quotient representative of Res_{x2}(h, x2^D-c2).
#
# Since x2^D-c2 splits over F_p on a valid fiber, its roots are roots2.
# Up to a nonzero sign, the resultant is the product of h(x1,b) over
# b in roots2.  We reduce x1^D=c1 after every multiplication, exactly
# as required by the fiber method.
# ----------------------------------------------------------------------
FiberResultantX2 := proc(h, roots2, c1, c2)
    local res, b, term:

    res := 1:

    for b in roots2 do
        term := FpRed(subs(x2 = b, h)):
        res := MulRed(res, term, [], c1, c2):
    end do:

    return FiberReduce(res, c1, c2)
end proc:

# ----------------------------------------------------------------------
# Small list/set helpers.
# ----------------------------------------------------------------------
PairMember := proc(q, L)
    local t:

    for t in L do
        if q[1] = t[1] and q[2] = t[2] then
            return true
        end if:
    end do:

    return false
end proc:

SamePairSets := proc(A, B)
    local q:

    if nops(A) <> nops(B) then
        return false
    end if:

    for q in A do
        if not PairMember(q, B) then
            return false
        end if:
    end do:

    return true
end proc:

# ----------------------------------------------------------------------
# Analyze one fixed fiber.
# Returns:
# [#GCD x1 candidates, #recovered pairs, #verified pairs,
#  #true pairs, build time, aux-elim time, input-elim/recovery time,
#  verified pairs, true pairs]
# ----------------------------------------------------------------------
AnalyzeFiber := proc(c1, c2)
    local roots1, roots2, trueSols, a, b, out,
          tmp, h, buildTime, auxTime,
          t0, Rx2, G, x1Cands, partial, verified, totalInputTime:

    roots1 := FiberRoots(c1):
    roots2 := FiberRoots(c2):

    if nops(roots1) <> DFiber or nops(roots2) <> DFiber then
        error "invalid fiber: expected exactly D roots"
    end if:

    # Brute-force ground truth inside this fiber (only D^2 points).
    trueSols := []:

    for a in roots1 do
        for b in roots2 do
            out := Permute([a, b, 0]):

            if out[KnownBranch + 1] = hprev then
                trueSols := [op(trueSols), [a, b]]:
            end if:
        end do:
    end do:

    # Symbolic construction + auxiliary elimination.
    tmp := BuildAndEliminateFiber(c1, c2):
    h := tmp[1]:
    buildTime := tmp[2]:
    auxTime := tmp[3]:

    # Symbolic-input elimination, GCD, recovery, and verification.
    t0 := time():

    Rx2 := FiberResultantX2(h, roots2, c1, c2):
    G := Gcd(Rx2, x1^DFiber - c1) mod p:
    G := FpRed(G):

    x1Cands := []:

    for a in roots1 do
        if FpRed(subs(x1 = a, G)) = 0 then
            x1Cands := [op(x1Cands), a]:
        end if:
    end do:

    partial := []:

    for a in x1Cands do
        for b in roots2 do
            if FpRed(subs(x1 = a, x2 = b, h)) = 0 then
                partial := [op(partial), [a, b]]:
            end if:
        end do:
    end do:

    verified := []:

    for tmp in partial do
        out := Permute([tmp[1], tmp[2], 0]):

        if out[KnownBranch + 1] = hprev then
            verified := [op(verified), tmp]:
        end if:
    end do:

    totalInputTime := time() - t0:

    # Check recovery against brute force on the fixed fiber.
    if not SamePairSets(verified, trueSols) then
        error "recovery mismatch on fiber (%1,%2)", c1, c2
    end if:

    return [nops(x1Cands), nops(partial), nops(verified),
            nops(trueSols), buildTime, auxTime, totalInputTime,
            verified, trueSols]
end proc:

# ======================================================================
# Fiber sample
# ======================================================================
CDset := {}:

for aa from 1 to p - 1 do
    CDset := CDset union {PowFp(aa, DFiber)}:
end do:

CD := sort(convert(CDset, list)):

if nops(CD) <> (p - 1)/DFiber then
    error "unexpected number of D-th-power values"
end if:

AllFibers := []:

for i from 1 to nops(CD) do
    for j from 1 to nops(CD) do
        AllFibers := [op(AllFibers), [CD[i], CD[j]]]:
    end do:
end do:

if NUM_FIBERS > nops(AllFibers) then
    error "NUM_FIBERS is too large"
end if:

# Full-cycle indexing; gcd(73,196)=1.
FiberPairs := [
    seq(AllFibers[1 + irem(73*(i - 1) + 41, nops(AllFibers))],
        i = 1 .. NUM_FIBERS)
]:

printf("============================================================\n"):
printf("Small-scale fiber experiment\n"):
printf("p=%d, alpha=%d, D=%d, R=%d, m=3, n_x=2\n",
       p, alpha, DFiber, R):
printf("|C_D|=%d, fiber size D^2=%d, sampled fibers=%d\n",
       nops(CD), DFiber^2, NUM_FIBERS):
printf("heuristic E[solutions/fiber] = %.6f\n",
       evalf(DFiber^2/p)):
printf("heuristic P(nonempty fiber) = %.4f%%\n",
       evalf(100*(1 - (1 - 1/p)^(DFiber^2)))):
printf("============================================================\n\n"):

Results := []:
totalGcd := 0:
totalPartial := 0:
totalVerified := 0:
totalTrue := 0:
fibersWithSolution := 0:
totalBuildTime := 0.0:
totalAuxTime := 0.0:
totalInputTime := 0.0:

for i from 1 to NUM_FIBERS do
    c1 := FiberPairs[i][1]:
    c2 := FiberPairs[i][2]:

    printf("--- fiber %d/%d: (c1,c2)=(%d,%d) ---\n",
           i, NUM_FIBERS, c1, c2):

    rec := AnalyzeFiber(c1, c2):

    nGcd := rec[1]:
    nPartial := rec[2]:
    nVerified := rec[3]:
    nTrue := rec[4]:
    tBuild := rec[5]:
    tAux := rec[6]:
    tInput := rec[7]:

    totalGcd := totalGcd + nGcd:
    totalPartial := totalPartial + nPartial:
    totalVerified := totalVerified + nVerified:
    totalTrue := totalTrue + nTrue:

    totalBuildTime := totalBuildTime + tBuild:
    totalAuxTime := totalAuxTime + tAux:
    totalInputTime := totalInputTime + tInput:

    if nTrue > 0 then
        fibersWithSolution := fibersWithSolution + 1
    end if:

    printf("GCD x1 candidates=%d, recovered pairs=%d, verified=%d, true=%d\n",
           nGcd, nPartial, nVerified, nTrue):
    printf("times: build=%.2f s, aux-elim=%.2f s, input/recovery=%.2f s\n",
           tBuild, tAux, tInput):

    if PRINT_SOLUTIONS and nVerified > 0 then
        printf("verified pairs = %a\n", rec[8])
    end if:

    Results := [op(Results),
                [i, c1, c2, nGcd, nPartial, nVerified, nTrue,
                 tBuild, tAux, tInput]]:

    printf("\n"):
end do:

printf("============================================================\n"):
printf("EXPERIMENT SUMMARY\n"):
printf("fibers tested                         : %d\n", NUM_FIBERS):
printf("GCD candidate x1 values              : %d\n", totalGcd):
printf("recovered (x1,x2) pairs              : %d\n", totalPartial):
printf("verified complete solutions          : %d\n", totalVerified):
printf("brute-force complete solutions       : %d\n", totalTrue):
printf("fibers containing >=1 solution       : %d\n", fibersWithSolution):
printf("average solutions per fiber          : %.6f\n",
       evalf(totalTrue/NUM_FIBERS)):
printf("empirical nonempty-fiber probability : %.4f%%\n",
       evalf(100*fibersWithSolution/NUM_FIBERS)):
printf("heuristic E[solutions/fiber]          : %.6f\n",
       evalf(DFiber^2/p)):
printf("heuristic nonempty-fiber probability : %.4f%%\n",
       evalf(100*(1 - (1 - 1/p)^(DFiber^2)))):
printf("total build time                     : %.2f s\n", totalBuildTime):
printf("total auxiliary-elimination time     : %.2f s\n", totalAuxTime):
printf("total input/recovery time             : %.2f s\n", totalInputTime):
printf("correctness                          : PASS\n"):
printf("============================================================\n"):

# Results is retained in the Maple session for optional further analysis.
