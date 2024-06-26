/******************************************************************************
 * B e n c h I T - Performance Measurement for Scientific Applications BIGConsole.java Author: SWTP
 * Nagel 1 Last change by: $Author: tschuet $ $Revision: 1.10 $ $Date: 2007/06/05 11:32:41 $
 ******************************************************************************/
package gui;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;

import javax.swing.*;
import javax.swing.text.*;

/**
 * The Console observes the standard output and standard error stream and displays both outputs with different styles.<br>
 * Everything coming over the standard output is for debuging level only, it were displayed in grey color.<br>
 * Everything coming over the standard error is for warnings or information to the user, it were displayed in black
 * color.<br>
 * If an exceptions is occured in the program it is also displayed in the console in bold red.<br>
 * <br>
 * The console is read only.
 * 
 * @see BIGConsole.ReaderThread
 * @author Carsten Luxig <a href="mailto:c.luxig@lmcsoft.com">c.luxig@lmcsoft.com</a>
 */
public class BIGConsole extends JFrame {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private PipedInputStream piOut;
	// private PipedInputStream piErr;
	private PipedOutputStream poOut;
	private JTextPane textPane;
	private JButton clearButton, closeButton, saveButton;
	private JScrollPane js;
	private JTextPane lineComponent;
	private Hashtable<String, Style> attr;
	private final StyleContext styleContext = new StyleContext();
	private final DefaultStyledDocument doc = new DefaultStyledDocument(styleContext);
	private final DefaultStyledDocument lineDoc = new DefaultStyledDocument(styleContext);
	private int rowCount = 0;

	/** The style type for warnings (std err). */
	public static final int WARNING = 0;
	/** The style type for errors (exceptions). */
	public static final int ERROR = 1;
	/** The style type for debuging (std out). */
	public static final int DEBUG = 2;

	/**
	 * Creates a console window with the given width and height in pixel.
	 * 
	 * @param width the width of the inner textpane
	 * @param height the height of the inner textpane
	 */
	public BIGConsole(int width, int height, InputStream[] str) throws IOException {
		createUI(width, height);

		// Create reader threads to observe the std out and std err
		try {
			if (str != null) {
				for (int i = 0; i < str.length; i++) {
					new ReaderThread(str[i], DEBUG).start();
				}
			}
		} catch (Exception exc) {
			System.err.println("BIGConsole: Exception occured during scaning the streams: " + exc);
		}

	}

	/**
	 * Creates a console window with the given width and height in pixel.
	 * 
	 * @param width the width of the inner textpane
	 * @param height the height of the inner textpane
	 */
	public BIGConsole(int width, int height) throws IOException {
		createUI(width, height);

		// Set up System.out
		piOut = new PipedInputStream();
		poOut = new PipedOutputStream(piOut);
		System.setOut(new PrintStream(poOut, true));

		// Set up System.err
		// piErr = new PipedInputStream();
		// System.setErr( new PrintStream( poErr , true ) ) ;

		// Create reader threads to observe the std out and std err
		try {
			new ReaderThread(piOut, DEBUG).start();
			// new ReaderThread(piErr, ERROR).start();
		} catch (Exception exc) {
			System.err.println("BIGConsole: Exception occured during scaning the streams: " + exc);
		}
	}

	private void createUI(int width, int height) {
		if (!SwingUtilities.isEventDispatchThread()) {
			final int w = width;
			final int h = height;
			try {
				SwingUtilities.invokeAndWait(new Runnable() {
					public void run() {
						createUI(w, h);
					}
				});
				return;
			} catch (Exception e) {
				System.err.println("Error creating console: " + e + "\n Trying unsafe create.");
			}
		}

		setDefaultCloseOperation(WindowConstants.HIDE_ON_CLOSE);
		// Add a text pane
		// no line wrap is possible by overriding this methods
		textPane = new JTextPane() {
			private static final long serialVersionUID = 1L;

			@Override
			public void setSize(Dimension d) {
				if (d.width < getParent().getSize().width) {
					d.width = getParent().getSize().width;
				}
				super.setSize(d);
			}

			@Override
			public boolean getScrollableTracksViewportWidth() {
				return false;
			}
		};
		textPane.setToolTipText("This console area will display errors, warnings, and "
				+ "information about the program or it's components.");
		textPane.setStyledDocument(doc);
		textPane.setFont(new Font("Monospaced", 0, 0));
		// the hash table for the styles
		attr = new Hashtable<String, Style>();

		int fontSize = system.BIGInterface.getInstance().getBIGConfigFileParser()
				.intCheckOut("consoleTextSize", 12);
		// none Style
		Style s = styleContext.addStyle("none", null);
		StyleConstants.setFontFamily(s, "Monospaced");
		StyleConstants.setFontSize(s, fontSize);
		attr.put("none", s);
		// Style for errors --> if exceptions thrown
		s = styleContext.addStyle("error", null);
		StyleConstants.setBold(s, true);
		StyleConstants.setItalic(s, false);
		StyleConstants.setForeground(s, Color.red);
		StyleConstants.setFontFamily(s, "Monospaced");
		StyleConstants.setFontSize(s, fontSize);
		attr.put("error", s);

		// Style for debug --> stdout pipe
		s = styleContext.addStyle("debug", null);
		StyleConstants.setBold(s, false);
		StyleConstants.setItalic(s, false);
		StyleConstants.setForeground(s, new Color(90, 90, 150));
		StyleConstants.setFontFamily(s, "Monospaced");
		StyleConstants.setFontSize(s, fontSize);
		attr.put("debug", s);

		// Style for lines
		s = styleContext.addStyle("line", null);
		StyleConstants.setBold(s, false);
		StyleConstants.setItalic(s, false);
		StyleConstants.setForeground(s, new Color(120, 120, 120));
		StyleConstants.setFontFamily(s, "Monospaced");
		StyleConstants.setFontSize(s, fontSize);
		// attr.put( "debug" , s ) ;
		attr.put("line", s);

		// Style for blind lines (place holder)
		s = styleContext.addStyle("blind_line", null);
		StyleConstants.setBold(s, false);
		StyleConstants.setItalic(s, false);
		StyleConstants.setForeground(s, new Color(200, 200, 200));
		StyleConstants.setFontFamily(s, "Monospaced");
		StyleConstants.setFontSize(s, fontSize);
		attr.put("blind_line", s);

		// default (for warnings) --> for stderr pipe
		Style def = styleContext.getStyle(StyleContext.DEFAULT_STYLE);
		StyleConstants.setForeground(def, Color.black);
		StyleConstants.setFontFamily(def, "Monospaced");
		StyleConstants.setFontSize(def, fontSize);
		attr.put("default", def);

		lineComponent = new JTextPane();
		lineComponent.setStyledDocument(lineDoc);
		lineComponent.setBackground(new Color(200, 200, 200));
		lineComponent.setEditable(false);
		// to init. the width of the line view
		try {
			lineDoc.insertString(0, "00000\n", attr.get("blind_line"));
		} catch (BadLocationException ble) {
			System.err.println("Wrong position in BIGConsole: " + ble);
		}

		textPane.setEditable(false);
		textPane.setBackground(new Color(230, 255, 220));
		js = new JScrollPane(textPane, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
				ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		js.setPreferredSize(new Dimension(width, height));
		js.setRowHeaderView(lineComponent);

		getContentPane().add(js, BorderLayout.CENTER);

		clearButton = new JButton("Clear");
		clearButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				textPane.setText("");
				lineComponent.setText("");
				// to init. the width of the line view
				try {
					lineDoc.insertString(0, "00000\n", attr.get("blind_line"));
				} catch (BadLocationException ble) {
					System.err.println("Wrong position in BIGConsole: " + ble);
				}
				rowCount = 0;
			}
		});

		saveButton = new JButton("Export");
		saveButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				// creating a log file from the current console window
				try {
					Calendar today = Calendar.getInstance();
					// with the current day as filename specification
					int month = today.get(Calendar.MONTH) + 1;
					String filename = "log" + File.separator + "console_" + today.get(Calendar.DAY_OF_MONTH)
							+ "_" + month + "_" + today.get(Calendar.YEAR) + "_"
							+ today.get(Calendar.HOUR_OF_DAY) + "_" + today.get(Calendar.MINUTE) + "_"
							+ today.get(Calendar.SECOND) + ".log";
					RandomAccessFile file = new RandomAccessFile(filename, "rw");
					file.writeBytes("This is the log from the BenchIT console.");
					file.writeByte(Character.LINE_SEPARATOR);
					file.writeBytes("It was created on " + today.getTime());
					file.writeByte(Character.LINE_SEPARATOR);
					file.writeByte(Character.LINE_SEPARATOR);

					String all[] = textPane.getText().split("\n");
					for (int i = 0; i < all.length; i++) {
						if (all[i].length() > 0) {
							// cut the last new line char
							all[i] = all[i].substring(0, all[i].length() - 1);
						}

						String s = (i + 1) + ": " + all[i];
						file.writeBytes(s);
					}
					file.close();
					System.err.println("File saved successfully to \"" + filename + "\".");
				} catch (IOException ioe) {
					System.err.println("BIGConsole: Error while writing in gog-File: " + ioe);
				}
			}
		});

		closeButton = new JButton("Close");
		closeButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				// unvisible (not really close) the window
				setVisible(false);
			}
		});

		// the button panel
		JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 5, 0));
		buttonPanel.add(clearButton);
		buttonPanel.add(saveButton);
		buttonPanel.add(closeButton);

		getContentPane().add(buttonPanel, BorderLayout.SOUTH);

		pack();
	}

	/**
	 * This Method can be used to get the displayed components as a panel in order to integrate it in a single window
	 * environment for example. This is done by the BIGGUI class to display the console output in the bottom part of the
	 * window.
	 * 
	 * @return a panel containing: a JScrollPane containing the displayed components AND buttons
	 */
	public JPanel getDisplayPanel() {
		return (JPanel) getContentPane();
	}

	public void postErrorMessage(String msg) {
		postMessage(msg, ERROR);
	}

	public void postDebugMessage(String msg) {
		postMessage(msg, DEBUG);
	}

	/**
	 * Posts a message in the console window. Use the type to set the style of the message.
	 * 
	 * @param msg the message print in the console
	 * @param type the message type<br>
	 *          possible values are:<br>
	 *          WARNING - default (std err) message type printed in black<br>
	 *          DEBUG - debug style (std out) printed in gray<br>
	 *          ERROR - error style for exceptions and errors<br>
	 */
	public void postMessage(String msg, int type) {
		msg += "\n";
		postMessageInternal(msg, type);
	}

	private void postMessageInternal(String msg, int type) {
		if (!SwingUtilities.isEventDispatchThread()) {
			SwingUtilities.invokeLater(new PostMessageDelayed(msg, type));
			return;
		}
		try {
			if (type == ERROR) {
				doc.insertString(doc.getLength(), msg, attr.get("error"));
			} else if (type == WARNING) {
				doc.insertString(doc.getLength(), msg, attr.get("none"));
			} else if (type == DEBUG) {
				doc.insertString(doc.getLength(), msg, attr.get("debug"));
			}
			// textPane.setCaretPosition( textPane.getText().length() );
		} catch (BadLocationException ble) {
			System.err.println("Wrong position in BIGConsole#postMessage: " + ble);
		}
		// Make sure the last line is always visible
		Dimension dim = textPane.getPreferredScrollableViewportSize();
		textPane.scrollRectToVisible(new Rectangle(0, dim.height, 1, 1));
		try {
			textPane.setCaretPosition(textPane.getText().length() - 1);
		} catch (IllegalArgumentException ignored) {

		}

		// checks and updates the number of lines
		checkLines();
	}

	/**
	 * Posts a message in the console window. Use the type to set the style of the message and brings up a message dialog.
	 * 
	 * @param msg the message print in the console
	 * @param type the message type<br>
	 *          possible values are:<br>
	 *          WARNING - default (std err) message type printed in black<br>
	 *          DEBUG - debug style (std out) printed in gray<br>
	 *          ERROR - error style for exceptions and errors<br>
	 * @param showConfirm whether to show a dialog with the given msg or not.
	 */
	public void postMessage(String msg, int type, boolean showConfirm) {
		postMessage(msg, type);

		// shows a message dialog with the specified params
		if (showConfirm) {
			String title = "";
			int msgType = 0;
			switch (type) {
				case WARNING :
					title = "Warning";
					msgType = JOptionPane.WARNING_MESSAGE;
					break;
				case ERROR :
					title = "Error";
					msgType = JOptionPane.ERROR_MESSAGE;
					break;
				case DEBUG :
					title = "Debug";
					msgType = JOptionPane.INFORMATION_MESSAGE;
					break;
			}

			// show dialog
			JOptionPane.showMessageDialog(null, msg, title, msgType);
		}
	}

	/**
	 * Posts a message in the console window using the standard style WARNING.
	 * 
	 * @param msg the message print in the console
	 * @see BIGConsole#postMessage(String msg, int type)
	 */
	public void postMessage(String msg) {
		postMessage(msg, WARNING);
	}

	/**
	 * Adds a input stream, from which the data read in the console window, with the given style type.
	 * 
	 * @param in the stream from which should be read
	 * @param type the style type<br>
	 *          - WARNING, ERROR, DEBUG
	 */
	public void addStream(InputStream in, int type) {
		try {
			new ReaderThread(in, type).start();
		} catch (Exception exc) {
			System.err.println("BIGConsole: Exception occured during scaning the streams: " + exc);
		}
	}

	public String getText() {
		return textPane.getText();
	}

	public void addReaderThread(ReaderThread rt) {
		readerThread.add(rt);
	}

	private void checkLines() {
		try {
			int curRowCount = textPane.getText().split("\n").length;
			// clear if the textpane has no rows
			if (rowCount <= 0) {
				lineComponent.setText("");
			}
			for (int i = rowCount + 1; i < curRowCount + 1; i++) {
				// fill in the place holder
				if (i < 10000) {
					lineDoc.insertString(lineDoc.getLength(), "0", attr.get("blind_line"));
				}
				if (i < 1000) {
					lineDoc.insertString(lineDoc.getLength(), "0", attr.get("blind_line"));
				}
				if (i < 100) {
					lineDoc.insertString(lineDoc.getLength(), "0", attr.get("blind_line"));
				}
				if (i < 10) {
					lineDoc.insertString(lineDoc.getLength(), "0", attr.get("blind_line"));
				}
				// fill in the line number
				lineDoc.insertString(lineDoc.getLength(), i + "\n", attr.get("line"));
			}

			// sets number of rows
			rowCount = curRowCount;
		} catch (BadLocationException ble) {
			System.err.println("Wrong position in BIGConsole: " + ble);
		}
	}

	Vector<ReaderThread> readerThread = new Vector<ReaderThread>();

	protected class PostMessageDelayed implements Runnable {
		private final String msg;
		private final int type;

		PostMessageDelayed(String msg, int type) {
			this.msg = msg;
			this.type = type;
		}
		public void run() {
			if (!msg.isEmpty())
				postMessageInternal(msg, type);
		}
	}

	/**
	 * This is the class to observe the pipes.
	 */
	protected class ReaderThread extends Thread {
		private final InputStream pi;
		private int type = WARNING;

		ReaderThread(InputStream pi, int type) {
			addReaderThread(this);
			this.pi = pi;
			this.type = type;
		}

		public InputStream getInputStream() {
			return pi;
		}

		@Override
		public void run() {
			byte[] buf = new byte[40000];
			int len;
			while (true) {
				try {
					len = pi.read(buf);
					if (len == -1)
						break;

					SwingUtilities.invokeLater(new PostMessageDelayed(new String(buf, 0, len), type));
				} catch (Exception exc) {
					// Pipe broken
					try {
						Thread.sleep(1000);
					} catch (InterruptedException ex) {}
					/*
					 * System.err.println( "BIGConsole: Exception occured during scaning the stream: " + exc);
					 */
				}
			}
			// System.out.println("Readerthread closed");
			readerThread.remove(this);
		}
	}
}
/*****************************************************************************
 * Log-History
 *****************************************************************************/
