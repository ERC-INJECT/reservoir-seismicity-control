import ReservoirSeismicityControl.Paper2026.PhysicalA7DimensionalWeakH2_20261027
import ReservoirSeismicityControl.Paper2026.PhysicalPressureNDMaximalSemigroup20261027
import ReservoirSeismicityControl.Paper2026.VerificationSpatialND_20261027

/-!
# n_d in {1,2,3}: concrete weak-H² and maximal weak-Neumann graph

The *same* n_d is used for the local second-derivative Sobolev graph,
physical permeability tensor, and maximal distributional pressure gradient.

Previously verified 3D and paper-wide theorems are imported but untouched.
The key improvement over the preceding ND semigroup checkpoint is that the
weak-gradient domain, graph closure and weak IBP are now constructed rather
than passed as arbitrary D, G, and hIBP. Density of the scalar weak domain
is derived from scalar-test density and the test-level Green identity.

As before, the existence and density of physical C_c^∞(Ω) realizations
in 1D/2D, equivalence with the usual Neumann H¹, and A10 physical generator
identification remain applicability questions, not silently discharged here.
-/

#check ReservoirSeismicityControl.Paper2026.PaperSpatialDimension
#check ReservoirSeismicityControl.Paper2026.A7DimensionalH2
#check ReservoirSeismicityControl.Paper2026.a7_dimensional_mem_H2_iff
#check ReservoirSeismicityControl.pressureNDTestGraph
#check ReservoirSeismicityControl.pressure_nd_test_graph_mem_iff
#check ReservoirSeismicityControl.pressure_nd_test_graph_closed
#check ReservoirSeismicityControl.pressure_nd_test_gradient_unique
#check ReservoirSeismicityControl.pressureNDWeakH1Candidate
#check ReservoirSeismicityControl.pressureNDWeakGradient
#check ReservoirSeismicityControl.pressure_nd_weak_gradient_ibp
#check ReservoirSeismicityControl.pressure_nd_weak_graph_eq_test_graph
#check ReservoirSeismicityControl.pressure_nd_weak_graph_embedding_injective
#check ReservoirSeismicityControl.pressure_nd_weak_H1_dense_of_scalar_tests
#check ReservoirSeismicityControl.pressure_nd_maximal_weak_A3_semigroup_exists
#print axioms ReservoirSeismicityControl.pressure_nd_weak_graph_eq_test_graph
#print axioms ReservoirSeismicityControl.pressure_nd_weak_H1_dense_of_scalar_tests
#print axioms ReservoirSeismicityControl.pressure_nd_maximal_weak_A3_semigroup_exists
