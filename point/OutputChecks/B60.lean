import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block60_checked : centerBlock 60 = true := by decide +kernel
#print axioms block60_checked
end PythiaCert.Output
