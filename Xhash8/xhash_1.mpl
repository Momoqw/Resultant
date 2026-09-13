restart:
interface(prettyprint = 0):
kernelopts(printbytes = false):

with(LinearAlgebra):

# ------------------------------------------------------------
#  Parameters
# ------------------------------------------------------------
alpha := 3:
p     := 2^16 - 17:                           # = 65519, prime
R     := 3:                                   # number of rounds

InvBranches := [0, 2]:
KnownBranch := 0:
hprev := '0':
BALANCED_DISPLAY := true:                     # print -1 instead of 65518

if igcd(alpha, p - 1) <> 1 then
    error "gcd(alpha, p-1) != 1, S-box not a permutation"
end if:

# ------------------------------------------------------------
#  Modular polynomial expand + balanced-form helper
# ------------------------------------------------------------
FpRed := proc(e)
    return Expand(e) mod p
end proc:

ToBalanced := proc(e)
    local ee, half:
    ee := Expand(e) mod p:
    half := iquo(p, 2):
    return subsindets(ee, integer,
        c -> `if`(c > half, c - p, c))
end proc:

# ------------------------------------------------------------
#  MDS matrix and round constants
# ------------------------------------------------------------
M := Matrix([[32760, 43679, 52415],
             [43679, 52415, 13104],
             [52415, 13104, 56159]]):

randomize():
RandFp := rand(0 .. p - 1):

C := Array(0 .. 9):
for k from 0 to 9 do
    C[k] := [RandFp(), RandFp(), RandFp()]:
end do:

# ------------------------------------------------------------
#  Vector ops
# ------------------------------------------------------------
AddC := proc(v, cvec)
    local i:
    return [seq(FpRed(v[i] + cvec[i]), i = 1 .. 3)]
end proc:

LinM := proc(v)
    local i, j:
    return [seq(FpRed(add(M[i, j] * v[j], j = 1 .. 3)), i = 1 .. 3)]
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

# ------------------------------------------------------------
#  Rewrite trick: y^alpha -> input via algsubs
# ------------------------------------------------------------
ReduceOne := proc(e, eq_list)
    local res, prev, j, yvar, input:

    res := FpRed(e):

    if nops(eq_list) = 0 then
        return res
    end if:

    do
        prev := res:

        for j from nops(eq_list) by -1 to 1 do
            yvar  := eq_list[j][1]:
            input := eq_list[j][2]:

            res := algsubs(yvar^alpha = input, res):
            res := Expand(res) mod p:
        end do:

        if res = prev then
            break
        end if:
    end do:

    return res
end proc:

ReduceState := proc(state, eq_list)
    local i:
    return [seq(ReduceOne(state[i], eq_list), i = 1 .. 3)]
end proc:

# ------------------------------------------------------------
#  Reduced arithmetic:
#  Reduce immediately after every multiplication/addition.
#  This keeps auxiliary variables below alpha-power during construction.
# ------------------------------------------------------------
MulRed := proc(u, v, eq_list)
    return ReduceOne(FpRed(u * v), eq_list)
end proc:

TermRed := proc(c, L, eq_list)
    local res, k:

    res := c:

    for k from 1 to nops(L) do
        res := MulRed(res, L[k], eq_list):
    end do:

    return res
end proc:

SumRed := proc(L, eq_list)
    local s, k:

    s := 0:

    for k from 1 to nops(L) do
        s := ReduceOne(FpRed(s + L[k]), eq_list):
    end do:

    return s
end proc:

Pow3Red := proc(u, eq_list)
    local u2, u3:

    u2 := MulRed(u, u, eq_list):
    u3 := MulRed(u2, u, eq_list):

    return u3
end proc:

SAlphaVecRed := proc(v, eq_list)
    local i:
    return [seq(Pow3Red(v[i], eq_list), i = 1 .. 3)]
end proc:

# ------------------------------------------------------------
#  Pi2 (P3 step) for alpha = 3 over
#  F_p[a]/(a^3 + a^2 + a + 5)
#
#  That is, a^3 = -a^2 - a - 5.
#  Reduced version: every cubic monomial is built through TermRed,
#  so reductions x_i^3 = pre_i are applied during construction.
# ------------------------------------------------------------

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

Pi2Red := proc(v, eq_list)
    local a, b, d, y0, y1, y2:

    a := v[1]:
    b := v[2]:
    d := v[3]:

    y0 := SumRed([
        TermRed(1,  [a, a, a], eq_list),
        TermRed(-5, [b, b, b], eq_list),
        TermRed(20, [d, d, d], eq_list),
        TermRed(15, [a, d, d], eq_list),
        TermRed(15, [b, b, d], eq_list),
        TermRed(-30, [a, b, d], eq_list)
    ], eq_list):

    y1 := SumRed([
        TermRed(3,  [a, a, b], eq_list),
        TermRed(-1, [b, b, b], eq_list),
        TermRed(4,  [d, d, d], eq_list),
        TermRed(-12, [a, d, d], eq_list),
        TermRed(-12, [b, b, d], eq_list),
        TermRed(15, [b, d, d], eq_list),
        TermRed(-6, [a, b, d], eq_list)
    ], eq_list):

    y2 := SumRed([
        TermRed(3,  [a, a, d], eq_list),
        TermRed(3,  [a, b, b], eq_list),
        TermRed(-1, [b, b, b], eq_list),
        TermRed(9,  [d, d, d], eq_list),
        TermRed(-12, [b, d, d], eq_list),
        TermRed(-6, [a, b, d], eq_list)
    ], eq_list):

    return [y0, y1, y2]
end proc:

# ============================================================
#  Build the polynomial system
# ============================================================
state   := [x, 0, 0]:
eq_list := []:
fx_list := []:
gx_list := []:
aux_idx := 0:

t_build := time():

for r to R do
    printf("=== round %d ===\n", r):

    # F step:
    # Use SAlphaVecRed instead of SAlphaVec so that each cubic power
    # is reduced immediately by previously generated equations.
    state := AffineBefore(state, C[3*r - 3]):
    state := SAlphaVecRed(state, eq_list):
    state := ReduceState(state, eq_list):
    printf("  after F (x^%d + immediate algsubs):  monomials = [%d, %d, %d]\n",
           alpha, NumMon(state[1]), NumMon(state[2]), NumMon(state[3])):

    pre := AffineAfter(state, C[3*r - 2]):
    printf("  after B' affine:                     pre       = [%d, %d, %d]\n",
           NumMon(pre[1]), NumMon(pre[2]), NumMon(pre[3])):

    state_after_B := pre:

    for br in InvBranches do
        idx     := br + 1:
        aux_idx := aux_idx + 1:
        yvar    := parse(cat("x", aux_idx)):

        # fxi := pre_i - xi^alpha
        fx_list := [op(fx_list), FpRed(pre[idx] - yvar^alpha)]:

        # gxi := xi^alpha = pre_i
        gx_list := [op(gx_list), yvar^alpha = pre[idx]]:

        # Store rewrite rule for immediate reductions in later construction.
        eq_list       := [op(eq_list), [yvar, pre[idx]]]:
        state_after_B := subsop(idx = yvar, state_after_B):
    end do:

    # P3 step:
    # Use Pi2Red instead of Pi2 so that products are reduced immediately.
    state := AddC(state_after_B, C[3*r - 1]):
    state := Pi2Red(state, eq_list):
    state := ReduceState(state, eq_list):
    printf("  after P3 (Pi2Red + immediate algsubs): monomials = [%d, %d, %d]\n",
           NumMon(state[1]), NumMon(state[2]), NumMon(state[3])):
end do:

out := AffineAfter(state, C[9]):
printf("after final MC:                          monomials = [%d, %d, %d]\n",
       NumMon(out[1]), NumMon(out[2]), NumMon(out[3])):

fh := FpRed(out[KnownBranch + 1] - hprev):

for i from 1 to aux_idx do
    assign(parse(cat("fx", i)), fx_list[i]):
    assign(parse(cat("gx", i)), gx_list[i]):
end do:

printf("\nGenerated polynomial equations: "):
for i from 1 to aux_idx do
    printf("fx%d, ", i)
end do:
printf("fh\n"):

printf("Generated substitution rules : "):
for i from 1 to aux_idx do
    printf("gx%d", i):
    if i < aux_idx then
        printf(", ")
    end if:
end do:
printf("\n"):

printf("(p = %d, alpha = %d, R = %d, build time %.2f s)\n",
       p, alpha, R, time() - t_build):

# ============================================================
#  Back-to-front elimination
#  MEMORY-SAFE version for equations of the form:
#
#      fx_i = A_i - x_i^3
#
#  If f = a0 + a1*y + a2*y^2 and y^3 = A, then
#
#      Resultant_y(f, A - y^3)
#        = a0^3 + A*a1^3 + A^2*a2^3 - 3*A*a0*a1*a2
#
#  This avoids building SylvesterMatrix and avoids Det(tt).
# ============================================================

PrefixEqs := proc(L, n)
    local k:
    if n <= 0 then
        return []
    end if:
    return [seq(L[k], k = 1 .. n)]
end proc:

CubicNormRed := proc(f, A, y, prev_eqs)
    local ff, AA, dy, a0, a1, a2, t0, t1, t2, t3, res:

    # First reduce all older variables so degree in each older x_j stays < 3.
    ff := ReduceOne(f, prev_eqs):
    ff := collect(ff, y):

    dy := degree(ff, y):

    if dy > 2 then
        error "degree in %1 is %2, expected <= 2 before cubic norm", y, dy
    end if:

    AA := ReduceOne(A, prev_eqs):

    a0 := ReduceOne(coeff(ff, y, 0), prev_eqs):
    a1 := ReduceOne(coeff(ff, y, 1), prev_eqs):
    a2 := ReduceOne(coeff(ff, y, 2), prev_eqs):

    # t0 = a0^3
    t0 := Pow3Red(a0, prev_eqs):

    # t1 = A*a1^3
    t1 := TermRed(1, [AA, Pow3Red(a1, prev_eqs)], prev_eqs):

    # t2 = A^2*a2^3
    t2 := TermRed(1, [AA, AA, Pow3Red(a2, prev_eqs)], prev_eqs):

    # t3 = -3*A*a0*a1*a2
    t3 := TermRed(-3, [AA, a0, a1, a2], prev_eqs):

    res := SumRed([t0, t1, t2, t3], prev_eqs):
    return res
end proc:

F1 := Array([seq(parse(cat("fx", i)), i = 1 .. aux_idx)]):
G1 := Array([seq(parse(cat("gx", i)), i = 1 .. aux_idx)]):
I1 := Array([seq(parse(cat("x",  i)), i = 1 .. aux_idx)]):

f_h := fh:

printf("\n========== memory-safe cubic-norm elimination ==========\n"):
printf("initial:                            deg_x(f_h) = %d\n",
       degree(f_h, x)):

t_elim := time():

for i from upperbound(I1) by -1 to 1 do
    printf("\n--- eliminating x%d ---\n", i):
    t_step := time():

    # Only older equations x1,...,x_{i-1} may appear in the coefficients.
    # We reduce with them during the norm computation.
    prev_eqs := PrefixEqs(eq_list, i - 1):

    # G1[i] has the form x_i^3 = A_i.
    A_i := rhs(G1[i]):

    f_h := CubicNormRed(f_h, A_i, I1[i], prev_eqs):
    f_h := ReduceOne(f_h, prev_eqs):

    gc():

    printf("  CubicNorm eliminate x%d:          deg_x = %d  (%.2f s)\n",
           i, degree(f_h, x), time() - t_step):
end do:

printf("\n=========================================\n"):
printf("final univariate equation in x:     deg_x = %d\n", degree(f_h, x)):
printf("total elimination time:             %.2f s\n", time() - t_elim):

# Optional display:
# f_h_balanced := ToBalanced(f_h):
# print(f_h_balanced):
