import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block134_checked : centerBlock 134 = true := by decide +kernel
#print axioms block134_checked
end PythiaCert.Output
