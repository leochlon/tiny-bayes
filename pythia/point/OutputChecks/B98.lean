import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block98_checked : centerBlock 98 = true := by decide +kernel
#print axioms block98_checked
end PythiaCert.Output
