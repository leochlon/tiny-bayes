import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block125_checked : centerBlock 125 = true := by decide +kernel
#print axioms block125_checked
end PythiaCert.Output
