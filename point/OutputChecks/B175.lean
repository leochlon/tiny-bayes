import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block175_checked : centerBlock 175 = true := by decide +kernel
#print axioms block175_checked
end PythiaCert.Output
