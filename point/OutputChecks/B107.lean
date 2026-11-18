import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block107_checked : centerBlock 107 = true := by decide +kernel
#print axioms block107_checked
end PythiaCert.Output
