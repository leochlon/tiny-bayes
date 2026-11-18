import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block171_checked : centerBlock 171 = true := by decide +kernel
#print axioms block171_checked
end PythiaCert.Output
