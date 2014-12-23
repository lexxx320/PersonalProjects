//Imports are listed in full to show what's being used 
//could just import javax.swing.* and java.awt.* etc.. 
import javax.swing.JFrame; 
import javax.swing.JPanel; 
import javax.swing.JComboBox; 
import javax.swing.JButton; 
import javax.swing.JLabel; 
import javax.swing.JList; 
import java.awt.BorderLayout; 
import java.awt.event.ActionListener; 
import java.awt.event.ActionEvent;  
import javax.swing.JFileChooser;
import java.io.*;

public class Main {  

    

    public static void main(String[] args) {
        JFrame guiFrame = new JFrame();  
        guiFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE); 
        guiFrame.setTitle("Credit Processor"); 
        guiFrame.setSize(300,250);  
        JPanel comboPanel = new JPanel(); 
        JLabel comboLbl = new JLabel("Select file to process"); 
        comboPanel.add(comboLbl); 
        
        JButton chooseFileButton = new JButton("Choose File");  

        
        class ButtonListener implements ActionListener{
            public void actionPerformed(ActionEvent event){
                JFileChooser chooser = new JFileChooser();
                chooser.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
                chooser.showOpenDialog(null);
                File f = chooser.getSelectedFile();
                FileProcessor processor = new FileProcessor(f);    
                while(!processor.done()){
                    try{
                        processor.process();
                    }catch(NotInDBException e){
                        //prompt user for input
                    }
                }
            }
        }
        chooseFileButton.addActionListener(new ButtonListener());  
        guiFrame.add(comboPanel, BorderLayout.NORTH); 
        guiFrame.add(chooseFileButton,BorderLayout.CENTER);  
        guiFrame.setVisible(true); 
    } 
}
