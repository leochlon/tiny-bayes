import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block18_checked : centerBlock 18 = true := by decide +kernel
#print axioms block18_checked
end PythiaCert.Output
