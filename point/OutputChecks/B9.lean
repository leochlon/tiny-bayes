import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block9_checked : centerBlock 9 = true := by decide +kernel
#print axioms block9_checked
end PythiaCert.Output
