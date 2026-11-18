Python scripts for the figures and the numbers of the paper
============================================================

figures\   one script per figure of the paper; each writes its PDF into figures\out\
numbers\   scripts that recompute the numbers of the examples, of the table "Schemes on the chain of three
           stores", of the figure captions and of the running text; each prints the computed value beside
           the value printed in the paper, says whether the two agree after rounding to the digits printed
           there, and ends with a count of the comparisons

Places in the paper are named by the title of the section, example, table or figure, not by number.


Packages
--------
numpy, scipy            all scripts
matplotlib              the scripts in figures\
cvxpy                   numbers\optimal_schemes.py and numbers\least_values.py only (with the solver
                        Clarabel, which cvxpy installs)

The figures use the font cmr10 that matplotlib ships. Tested with Python 3.14, numpy 2.5, scipy 1.18,
matplotlib 3.11 and cvxpy 1.9.


How to run
----------
With uv (https://docs.astral.sh/uv/), from the folder of the script:

    cd figures
    uv run --no-project --with numpy --with scipy --with matplotlib python fig_models.py

    cd numbers
    uv run --no-project --with numpy --with scipy python chain_table.py
    uv run --no-project --with numpy --with scipy --with cvxpy python optimal_schemes.py
    uv run --no-project --with numpy --with scipy --with cvxpy python least_values.py

Without uv: install the packages and run "python <script>.py" from the folder of the script. The scripts
import a module of their own folder (style.py, chain3.py or cosim.py), so they must be run from that folder
and without the option -I of Python. If cvxpy has no binary package for the newest Python, choose an earlier
one (with uv: add --python 3.14). Every script runs in a few seconds, except optimal_schemes.py, which takes
about one minute, and least_values.py, which takes a few minutes. No script reads or writes a file other than the PDFs in figures\out\.


figures\
--------
script                  figure of the paper (file written)        computed in the script
style.py                (module) sizes, type, colours and the drawing elements shared by all figures
chain3.py               (module) the chain of three stores and its shifted system, for fig_stability.py
fig_models.py           the networks of the examples (out\models.pdf)                    drawing only
fig_energy_circle.py    the two parts of the difference on an undamped pair, in energy   closed forms of the example
                        coordinates (out\energy_circle.pdf)                              "zero-order hold on an undamped pair"
fig_halfstep.py         one macro step: old and new sample (out\halfstep.pdf)            drawing only
fig_stability.py        the two ways of losing stability on the chain of three           eigenvalues of the shifted system;
                        (out\stability.pdf)                                              prints where the pair meets the real axis
fig_blocks.py           what the coefficients of a scheme reach: the blocks of X - U     drawing only
                        (out\blocks.pdf)
fig_order.py            the order of execution on the chain of three (out\order.pdf)     X - U and the two parts of the difference
                                                                                         of the zero-order holds at h = 0.1; asserts
                                                                                         the integers drawn
fig_visibility.py       the bound on the one-step error on the chain of three, Jacobi    bound and zero-order holds against h; the
                        scheme (out\visibility.pdf)                                      circles are values of optimal_schemes.py
fig_reach.py            more held samples on a lossless chain of six stores              the bound f_1 for 1 to 4 held samples
                        (out\reach.pdf)
fig_trade.py            energy injected against damping added on the chain of three      marks are values of optimal_schemes.py and
                        (out\trade.pdf)                                                  order_of_execution.py
fig_energy_run.py       the largest energy over a run on the lossless chain of three     ||X^k||^2 for the three zero-order holds
                        (out\energy_run.pdf)                                             and the energy-conserving sweep
fig_ports.py            the two-mass oscillator in four choices of port (out\ports.pdf)  drawing only; the growth rates beside the
                                                                                         titles are computed by two_mass_ports.py


numbers\
--------
script                  what it computes                                                 where in the paper
cosim.py                (module) zero-order hold with and without local gains, the       -
                        gains of the reaction, the bound alpha_*, the relative
                        one-step map, the modified system, the printing of comparisons
undamped_pair.py        zero-order hold on two stores: logarithm of X = I + hJ (lag      example "zero-order hold on an undamped
                        h - arctan h, energy factor 1 + h^2); sequential scheme:         pair"; figure of the energy circle; the
                        conserved quadratic form, leapfrog frequency, limit h = 2        sentences on two stores in the sections
                                                                                         "Modes and stability" and "Energy stored
                                                                                         and energy created"
stability_thresholds.py chain of three: the Cayley transform of the pencil (A, E);       section "Modes and stability" (h = 0.05 and
                        Jacobi threshold h = 0.05; E singular at h = 1.415 in every      h = 1.415 in the text and in the caption of
                        sequential order; positions of the marks of the figure           the figure of the two ways of losing
                                                                                         stability)
held_samples.py         the constants gamma (1/2, 5/12, 3/8; -1/2, -1/12, -1/24); f_1    section "The half step with more held
                        of the end store of a lossless chain of six against              samples" and its figure; the constants
                        gamma h^(l+1); the exact rule tan(wH/sqrt 2)/sqrt 2 on the       0.35, 0.65, 2.65, 1.42, 5.3 of the bound
                        lossless chain of three with two held samples                    over a run (theorem "order barrier",
                                                                                         appendix)
order_of_execution.py   chain of three, zero-order holds: entries of X - U and of the    figure of the order of execution; section
                        numerical dissipation between the end stores; star with three    "The coupling graph" (3, 1.5, 1; 1.001
                        leaves: forced entries and least trace 3, 1.5, 1; the            alpha_*; nu = 0; 0.033 h^3); mark "from end
                        energy-conserving sweep with and without dissipation;            to end" of the figure of the trade; section
                        lossless chain: injection alpha_* and 2 alpha_*, bound 1.15,     "Energy stored and energy created" and the
                        threshold sqrt 2                                                 figure of the energy over a run
optimal_schemes.py      chain of three at h = 0.1: the scheme with local gains that      example "the chain of three, by order of
                        has the smallest one-step error, and the one with the            execution" (the six values); marks of the
                        smallest one-step error among those that inject no energy,       figure of the trade and the 12 % and 2 % of
                        in a Jacobi scheme, with the middle store first and from end     its caption; example "the chain of three
                        to end; stable Jacobi schemes at the bound for h = 0.1, 0.2,     stores" (within a relative 1e-5 of the
                        0.3, 0.5                                                         bound); circles of the figure of the bound
chain_table.py          chain of three at h = 0.1: one-step error, injected energy,      table "Schemes on the chain of three stores"
                        shifts of the two decay rates and error over the run for the     (every entry); section "Common schemes on
                        zero-order holds, the holds with the gains K_i, linear           the chain of three" (running text); examples
                        extrapolation and the derivative of the partner output;          "supplying the reaction on the chain of three"
                                                                                         and "the chain of three stores" (alpha_* =
                        stability limits with the gains; a Jacobi scheme with the        0.0050, 2.0 to 2.2); end of the section
                        spectrum of the monolithic system                                "Convergence over a run"; section "Where the
                                                                                         reaction can be taken from" (X - U = O(H^3))
two_mass_ports.py       two-mass oscillator in four partitions: growth rates of the      figure of the four choices of port (the
                        two modes to leading order and from the eigenvalues of X at      rates beside the titles, "within 0.3 %");
                        H = 0.05; velocity and force at H = 0.1: alpha_*, diagonal       example "one oscillator, four choices of
                        blocks, total damping, one-step errors and spectral radii        port" (all numbers); the value f_1 =
                        with and without the gains K_i; conservation of the energy       0.50 H^2 in the example "the chain of three
                        with two displacements; alternating order; f_1 with force        stores"
                        and displacement
least_values.py         the least values over all schemes to leading order, from the      lemma "the reach of the coefficients" and
                        convex programmes over the reach of the coefficients: least      what follows: proposition "least one-step
                        one-step error on the chain (every order) and the star; the      error" (3/4, 1.06); example "the chain of
                        same without injection on the chain; least spread on the         three stores"; theorem "the amount" and the
                        chain and on stars with 3 to 6 leaves; least injection with      star with m leaves (1.5, 1, m/2); example
                        partner weights only (chain, star, ring of four); largest        "the chain of three, by order of execution"
                        energy over a run on the lossless chain; least error over a      (2 alpha_*); remark after "the reaction"
                        run on the chain against the zero-order holds                    (twice); section "Energy stored and energy
                                                                                         created" (1.15); the display after the
                                                                                         theorem "order barrier" (0.16, 0.33 to 0.35)


Global optima and results of a local search (optimal_schemes.py)
----------------------------------------------------------------
In a Jacobi scheme the one-step error is a convex function of all coefficients, and the two Jacobi values of
the example "the chain of three, by order of execution" (1.000 and 1.759 alpha_*) are global optima of convex
programmes. In the two sequential orders the two coefficients of the new samples are varied by the
Nelder-Mead method from four starting points (fixed seed), with a convex programme for the remaining
coefficients at each of them: 0.993 and 1.963 alpha_* (middle store first) and 1.000 and 1.000 alpha_* (from
end to end) are the smallest values found by this local search and are upper bounds of the minima. The search
is rerun at every call; no stored result is used. From end to end the minimiser is not unique; the mark of
the figure of the trade for this order is the energy-conserving sweep, computed in order_of_execution.py.
