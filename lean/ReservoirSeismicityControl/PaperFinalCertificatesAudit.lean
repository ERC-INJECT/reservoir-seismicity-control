import ReservoirSeismicityControl.PaperPhysicalDemandFinalCertificates
import ReservoirSeismicityControl.PaperGainContraction
import ReservoirSeismicityControl.PaperProofBridge

/-!
# Stage 57: final certificate audit, not a new tracking theorem

This module makes the end-to-end FINITE-DIMENSIONAL certificates easily
inspectable and asks Lean to print their actual kernel dependencies.

Theorem 1's existing normalized perturbation certificate is abstract in its
input gain/perturbation. Stage 56 provides the stronger, actual physical matrix
certificate for Theorem 2, conditional on the stated Appendix A and B inputs.

This audit does not assert the full PDE–ODE well-posedness theorem, the complete
MIMO super-twisting stability theorem from the external reference, or automatic
actuator/demand feasibility. No hypotheses on Qdot or Qddot are added here.
-/

-- Original controller: gain contraction + a.e. perturbation derivative,
-- still parameterized by the abstract continuous-linear-map gain and Psi.
#check ReservoirSeismicityControl.paper_theorem1_actual_derivative_from_contraction_ae
#print axioms ReservoirSeismicityControl.paper_theorem1_actual_derivative_from_contraction_ae

-- Algebraic exact-demand property proved in the abstract demand model.
#check ReservoirSeismicityControl.paper_theorem2_exact_demand_bridge
#print axioms ReservoirSeismicityControl.paper_theorem2_exact_demand_bridge

-- Demand controller: Appendix B vertex-to-physical-gain contraction.
#check ReservoirSeismicityControl.paper_physical_demand_contraction_from_vertices
#print axioms ReservoirSeismicityControl.paper_physical_demand_contraction_from_vertices

-- Stage 53/55: real, representation-independent physical matrix derivatives.
#check ReservoirSeismicityControl.paper_physical_wellCLM_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.paper_physical_wellCLM_hasDerivAt_ae
#check ReservoirSeismicityControl.paper_physical_gainCLM_hasDerivAt_ae
#print axioms ReservoirSeismicityControl.paper_physical_gainCLM_hasDerivAt_ae

-- Stage 56: actual physical normalized demand-perturbation rate and contraction.
#check ReservoirSeismicityControl.paper_physical_theorem2_certificates_from_vertices_ae
#print axioms ReservoirSeismicityControl.paper_physical_theorem2_certificates_from_vertices_ae
