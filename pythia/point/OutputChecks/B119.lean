import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block119_checked : centerBlock 119 = true := by decide +kernel
#print axioms block119_checked
end PythiaCert.Output
