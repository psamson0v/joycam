# Point-and-shoot camera for Raspberry Pi w/camera and Adafruit PiTFT.
# This must run as root (sudo python cam.py) due to framebuffer, etc.
#
# Adafruit invests time and resources providing this open source code,
# please support Adafruit and open-source development by purchasing
# products from Adafruit, thanks!
#
# http://www.adafruit.com/products/998  (Raspberry Pi Model B)
# http://www.adafruit.com/products/1367 (Raspberry Pi Camera Board)
# http://www.adafruit.com/products/1601 (PiTFT Mini Kit)
# This can also work with the Model A board and/or the Pi NoIR camera.
#
# Prerequisite tutorials: aside from the basic Raspbian setup and
# enabling the camera in raspi-config, you should configure WiFi (if
# using wireless with the Dropbox upload feature) and read these:
# PiTFT setup (the tactile switch buttons are not required for this
# project, but can be installed if you want them for other things):
# http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi
# Dropbox setup (if using the Dropbox upload feature):
# http://raspi.tv/2013/how-to-use-dropbox-with-raspberry-pi
#
# Written by Phil Burgess / Paint Your Dragon for Adafruit Industries.
# BSD license, all text above must be included in any redistribution.

import atexit
import _pickle as pickle
import errno
import fnmatch
import io
import os
import os.path
from picamera2 import Picamera2
import pygame
import stat
import threading
import time
import yuv2rgb
import cv2
from pygame.locals import *
from subprocess import call
import queue

# UI classes ---------------------------------------------------------------

# Small resistive touchscreen is best suited to simple tap interactions.
# Importing a big widget library seemed a bit overkill.  Instead, a couple
# of rudimentary classes are sufficient for the UI elements:

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.


class Icon:

    def __init__(self, name):
        self.name = name
        try:
            self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
        except BaseException:
            pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.
 
def fitBlit(rect, bitmap, screen, smooth=False):
    if bitmap is None:
        return

    scaledWidth = bitmap.get_width() / rect[2]
    scaledHeight = bitmap.get_height() / rect[3]
    scaleFactor = max(scaledWidth, scaledHeight)
    if smooth:
        transformed = pygame.transform.smoothscale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))
    else:
        transformed = pygame.transform.scale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))
 
    screen.blit(transformed,
                    (int(rect[0] + (rect[2] - bitmap.get_width() / scaleFactor) / 2),
                     int(rect[1] + (rect[3] - bitmap.get_height() / scaleFactor) / 2)))

def fillBlit(rect, bitmap, screen, smooth=False):
    if bitmap is None:
        return

    scaledWidth = bitmap.get_width() / rect[2]
    scaledHeight = bitmap.get_height() / rect[3]
    scaleFactor = min(scaledWidth, scaledHeight)
    if smooth:
        transformed = pygame.transform.smoothscale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))
    else:
        transformed = pygame.transform.scale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))

    screen.blit(transformed,
                    (int(rect[0] + (rect[2] - bitmap.get_width() / scaleFactor) / 2),
                     int(rect[1] + (rect[3] - bitmap.get_height() / scaleFactor) / 2)))


class Button:

    def __init__(self, rect, **kwargs):
        self.rect = rect  # Bounds
        self.color = None  # Background fill color, if any
        self.iconBg = None  # Background Icon (atop color fill)
        self.iconFg = None  # Foreground Icon (atop background)
        self.bg = None  # Background Icon name
        self.fg = None  # Foreground Icon name
        self.callback = None  # Callback function
        self.value = None  # Value passed to callback
        for key, value in kwargs.items():
            if key == 'color':
                self.color = value
            elif key == 'bg':
                self.bg = value
            elif key == 'fg':
                self.fg = value
            elif key == 'cb':
                self.callback = value
            elif key == 'value':
                self.value = value

    def selected(self, pos):
        x1 = self.rect[0]
        y1 = self.rect[1]
        x2 = x1 + self.rect[2] - 1
        y2 = y1 + self.rect[3] - 1
        if ((pos[0] >= x1) and (pos[0] <= x2) and
                (pos[1] >= y1) and (pos[1] <= y2)):
            if self.callback:
                if self.value is None:
                    self.callback()
                else:
                    self.callback(self.value)
            return True
        return False

    def draw(self, screen):
        if self.color:
            screen.fill(self.color, self.rect)
        if self.iconBg:
            fitBlit(self.rect, self.iconBg.bitmap, screen)
        if self.iconFg:
            fitBlit(self.rect, self.iconFg.bitmap, screen)

    def setBg(self, name):
        if name is None:
            self.iconBg = None
        else:
            for i in icons:
                if name == i.name:
                    self.iconBg = i
                    break


# UI callbacks -------------------------------------------------------------
# These are defined before globals because they're referenced by items in
# the global buttons[] list.

def isoCallback(n):  # Pass 1 (next ISO) or -1 (prev ISO)
    global isoMode
    setIsoMode((isoMode + n) % len(isoData))


def settingCallback(n):  # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    # Modes 1 and 2 are special modes you shouldn't be able to navigate into
    acceptableModes = (0, 3, 4, 5, 6, 7, 8)

    # You can't navigate out of these normally
    if screenMode not in acceptableModes:
        return

    position = acceptableModes.index(screenMode)
    position += n
    position %= len(acceptableModes)
    screenMode = acceptableModes[position]


def fxCallback(n):  # Pass 1 (next effect) or -1 (prev effect)
    global fxMode
    setFxMode((fxMode + n) % len(fxData))


def quitCallback():  # Quit confirmation button
    saveSettings()
    raise SystemExit


def viewCallback(n):  # Viewfinder buttons
    global loadIdx, scaled, screenMode, screenModePrior, settingMode, storeMode

    if n == 0:   # Gear icon (settings)
        screenMode = settingMode  # Switch to last settings mode
    elif n == 1:  # Play icon (image playback)
        if scaled:  # Last photo is already memory-resident
            loadIdx = saveIdx
            screenMode = 0  # Image playback
            screenModePrior = -1  # Force screen refresh
        else:      # Load image
            r = imgRange(pathData[storeMode])
            if r:
                showImage(r[1])  # Show last image in directory
            else:
                screenMode = 2  # No images
    else:  # Rest of screen = shutter
        takePicture()


def doneCallback():  # Exit settings
    global screenMode, settingMode
    if screenMode > 3:
        settingMode = screenMode
        saveSettings()
    screenMode = 3  # Switch back to viewfinder mode


screen = None  # Ugly hack to get the image viewer to load well


def spinner():
    global busy, screenMode, screenModePrior, screen

    # screen is not ready
    if not screen:
        return
    buttons[screenMode][3].setBg('working')
    buttons[screenMode][3].draw(screen)
    pygame.display.update()

    busy = True
    n = 0
    while busy is True:
        buttons[screenMode][4].setBg('work-' + str(n))
        buttons[screenMode][4].draw(screen)
        pygame.display.update()
        n = (n + 1) % 5
        time.sleep(0.15)

    buttons[screenMode][3].setBg(None)
    buttons[screenMode][4].setBg(None)
    screenModePrior = -1  # Force refresh


def imgRange(path):
    min = 9999
    max = 0
    try:
        for file in os.listdir(path):
            if fnmatch.fnmatch(file, 'IMG_[0-9][0-9][0-9][0-9].JPG'):
                i = int(file[4:8])
                if (i < min):
                    min = i
                if (i > max):
                    max = i
    finally:
        return None if min > max else (min, max)


def showNextImage(direction):
    global busy, loadIdx

    t = threading.Thread(target=spinner)
    t.start()

    n = loadIdx
    while True:
        n += direction
        if (n > 9999):
            n = 0
        elif (n < 0):
            n = 9999
        if os.path.exists(pathData[storeMode] + '/IMG_' + '%04d' % n + '.JPG'):
            showImage(n)
            break

    busy = False
    t.join()


def showImage(n):
    global busy, loadIdx, scaled, screenMode, screenModePrior, sizeMode, storeMode

    t = threading.Thread(target=spinner)
    t.start()

    img = pygame.image.load(
        pathData[storeMode] + '/IMG_' + '%04d' % n + '.JPG')
    scaled = pygame.transform.scale(img, sizeData[sizeMode][1])
    loadIdx = n

    busy = False
    t.join()

    screenMode = 0  # Photo playback
    screenModePrior = -1  # Force screen refresh


def imageCallback(n):  # Pass 1 (next image), -1 (prev image) or 0 (delete)
    global screenMode
    if n == 0:
        screenMode = 1  # Delete confirmation
    else:
        showNextImage(n)


def deleteCallback(n):  # Delete confirmation
    global loadIdx, scaled, screenMode, storeMode

    # Program returning to delete screen? Not inited yet
    if not screen:
        return

    screenMode = 0
    screenModePrior = -1
    if n is True:
        os.remove(pathData[storeMode] + '/IMG_' + '%04d' % loadIdx + '.JPG')
        if (imgRange(pathData[storeMode])):
            screen.fill(0)
            pygame.display.update()
            showNextImage(-1)
        else:  # Last image deleteted; go to 'no images' mode
            screenMode = 2
            scaled = None
            loadIdx = -1


def storeModeCallback(n):  # Radio buttons on storage settings screen
    global storeMode
    buttons[4][storeMode + 3].setBg('radio3-0')
    storeMode += n
    storeMode %= len(sizeData)
    buttons[4][storeMode + 3].setBg('radio3-1')


def sizeModeCallback(n):  # Radio buttons on size settings screen
    global sizeMode
    # Size mode should never be out of bounds, but it might be!
    buttons[5][sizeMode + 3].setBg('radio3-0')
    sizeMode+=n
    sizeMode %= len(sizeData)
    buttons[5][sizeMode + 3].setBg('radio3-1')
    camera.still_configuration.main.size = sizeData[n][0]
    camera.stop()
    camera.configure("still")
    camera.still_configuration.align()
    camera.start()
# camera.resolution = sizeData[sizeMode][1]
# camera.crop       = sizeData[sizeMode][2]


# Global stuff -------------------------------------------------------------

screenMode = 3      # Current screen mode; default = viewfinder
screenModePrior = -1      # Prior screen mode (for detecting changes)
settingMode = 4      # Last-used settings mode (default = storage)
storeMode = 0      # Storage mode; default = Photos folder
storeModePrior = -1      # Prior storage mode (for detecting changes)
sizeMode = 0      # Image size; default = Large
fxMode = 0      # Image effect; default = Normal
isoMode = 0      # ISO settingl default = Auto
iconPath = 'icons'  # Subdirectory containing UI bitmaps (PNG format)
saveIdx = -1      # Image index for saving (-1 = none set yet)
loadIdx = -1      # Image index for loading
scaled = None    # pygame Surface w/last-loaded image
screen_height = 240     # TFT display height
screen_width = 240     # TFT display width
imageQueue = queue.Queue()

# To use Dropbox uploader, must have previously run the dropbox_uploader.sh
# script to set up the app key and such.  If this was done as the normal pi
# user, set upconfig to the .dropbox_uploader config file in that account's
# home directory.  Alternately, could run the setup script as root and
# delete the upconfig line below.
uploader = '/home/pi/Dropbox-Uploader/dropbox_uploader.sh'
upconfig = '/home/pi/.dropbox_uploader'

sizeData = [  # Camera parameters for different size settings
    # Full res      Viewfinder  Crop window
    [(4000, 3000), (240, 240), (0.0, 0.0, 1.0, 1.0)],  # 12 MP
    [(3840, 2160), (240, 240), (0.0, 0.0, 1.0, 1.0)],  # 8 MP / 4K HD
    [(2592, 1944), (240, 240), (0.0, 0.0, 1.0, 1.0)],  # 5 MP
]

isoData = [  # Values for ISO settings [ISO value, indicator X position]
    [0, 27], [100, 64], [200, 97], [320, 137],
    [400, 164], [500, 197], [640, 244], [800, 297]]

# A fixed list of image effects is used (rather than polling
# camera.IMAGE_EFFECTS) because the latter contains a few elements
# that aren't valid (at least in video_port mode) -- e.g. blackboard,
# whiteboard, posterize (but posterise, British spelling, is OK).
# Others have no visible effect (or might require setting add'l
# camera parameters for which there's no GUI yet) -- e.g. saturation,
# colorbalance, colorpoint.
fxData = [
    'none', 'sketch', 'gpen', 'pastel', 'watercolor', 'oilpaint', 'hatch',
    'negative', 'colorswap', 'posterise', 'denoise', 'blur', 'film',
    'washedout', 'emboss', 'cartoon', 'solarize']

pathData = [
    '/home/pi/Photos',     # Path for storeMode = 0 (Photos folder)
    '/boot/DCIM/CANON999',  # Path for storeMode = 1 (Boot partition)
    '/home/pi/Photos']     # Path for storeMode = 2 (Dropbox)

icons = []  # This list gets populated at startup

# buttons[] is a list of lists; each top-level list element corresponds
# to one screen mode (e.g. viewfinder, image playback, storage settings),
# and each element within those lists corresponds to one UI button.
# There's a little bit of repetition (e.g. prev/next buttons are
# declared for each settings screen, rather than a single reusable
# set); trying to reuse those few elements just made for an ugly
# tangle of code elsewhere.

# Scaling button sized dynamically to screen resolution.
# The old camera project hardcoded these to fit 320x240


def scaleHeight(height):
    return int(height * screen_height / 240)


def scaleWidth(width):
    return int(width * screen_width / 320)


buttons = [
    # Screen mode 0 is photo playback
    [   Button((0, scaleWidth(188), screen_width, scaleHeight(52)), ), # We don't need the done button anymore, but the layout is hardcoded
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=imageCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=imageCallback, value=1),
        Button((scaleWidth(88), scaleHeight(70), scaleWidth(157),
               scaleHeight(102))),  # 'Working' label (when enabled)
        Button((scaleWidth(148), scaleHeight(129), scaleWidth(
            22), scaleHeight(22))),  # Spinner (when enabled)
        Button((scaleWidth(121), 0, scaleWidth(78), scaleHeight(52)), bg='trash', cb=imageCallback, value=0)],

    # Screen mode 1 is delete confirmation
    [Button((0, scaleHeight(35), scaleWidth(320), scaleHeight(33)), bg='delete'),
        Button((scaleWidth(32), scaleHeight(86), scaleWidth(120), scaleHeight(100)), bg='yn', fg='yes',
               cb=deleteCallback, value=True),
        Button((scaleWidth(168), scaleHeight(86), scaleWidth(120), scaleHeight(100)), bg='yn', fg='no',
               cb=deleteCallback, value=False)],

    # Screen mode 2 is 'No Images'
    [Button((0, 0, scaleWidth(320), scaleHeight(240)), cb=doneCallback),  # Full screen = button
        # Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)),
        # bg='done'),       # Fake 'Done' button
        Button((0, scaleHeight(53), scaleWidth(320), scaleHeight(80)), bg='empty')],     # 'Empty' message

    # Screen mode 3 is viewfinder / snapshot
    [Button((0, scaleHeight(188), scaleWidth(156), scaleHeight(52)), bg='gear', cb=viewCallback, value=0),
        Button((scaleWidth(164), scaleHeight(188), scaleWidth(156),
               scaleHeight(52)), bg='play', cb=viewCallback, value=1),
        Button((0, 0, scaleWidth(320), scaleHeight(240)),
               cb=viewCallback, value=2),
        Button((scaleWidth(88), scaleHeight(51), scaleWidth(157),
               scaleHeight(102))),  # 'Working' label (when enabled)
        Button((scaleWidth(148), scaleHeight(110), scaleWidth(22), scaleHeight(22)))],  # Spinner (when enabled)

    # Remaining screens are settings modes

    # Screen mode 4 is storage settings
    [   Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))), # We don't need the done button anymore, but the layout is hardcoded
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=settingCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=settingCallback, value=1),
        Button((scaleWidth(2), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-1', fg='store-folder',
               cb=storeModeCallback, value=0),
        Button((scaleWidth(110), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='store-boot',
               cb=storeModeCallback, value=1),
        Button((scaleWidth(218), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='store-dropbox',
               cb=storeModeCallback, value=2),
        Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(35)), bg='storage')],

    # Screen mode 5 is size settings
    [   Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))), # We don't need the done button anymore, but the layout is hardcoded
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=settingCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=settingCallback, value=1),
        Button((scaleWidth(2), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-1', fg='size-l',
               cb=sizeModeCallback, value=0),
        Button((scaleWidth(110), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='size-m',
               cb=sizeModeCallback, value=1),
        Button((scaleWidth(218), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='size-s',
               cb=sizeModeCallback, value=2),
        Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(29)), bg='size')],

    # Screen mode 6 is graphic effect
    [   Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))), # We don't need the done button anymore, but the layout is hardcoded:
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=settingCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=settingCallback, value=1),
        Button((0, scaleHeight(70), scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=fxCallback, value=-1),
        Button((scaleWidth(240), scaleHeight(70), scaleWidth(80),
               scaleHeight(52)), bg='next', cb=fxCallback, value=1),
        Button((0, scaleHeight(67), scaleWidth(320), scaleHeight(91)), bg='fx-none'),
        Button((0, scaleHeight(11), scaleWidth(320), scaleHeight(29)), bg='fx')],

    # Screen mode 7 is ISO
    [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)), bg='done', cb=doneCallback),
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=settingCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=settingCallback, value=1),
        Button((0, scaleHeight(70), scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=isoCallback, value=-1),
        Button((scaleWidth(240), scaleHeight(70), scaleWidth(80),
               scaleHeight(52)), bg='next', cb=isoCallback, value=1),
        Button((0, scaleHeight(79), scaleWidth(
            320), scaleHeight(33)), bg='iso-0'),
        Button((scaleWidth(9), scaleHeight(134), scaleWidth(302), scaleHeight(26)), bg='iso-bar'),
        Button((0, scaleHeight(157), scaleWidth(
            21), scaleHeight(19)), bg='iso-arrow'),
        Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(29)), bg='iso')],

    # Screen mode 8 is quit confirmation
    [  # Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)), bg='done', cb=doneCallback),
        Button((0, 0, scaleWidth(80), scaleHeight(52)),
               bg='prev', cb=settingCallback, value=-1),
        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
               bg='next', cb=settingCallback, value=1),
        Button((scaleWidth(110), scaleHeight(60), scaleWidth(100),
               scaleHeight(120)), bg='quit-ok', cb=quitCallback),
        Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(35)), bg='quit')]
]

# Assorted utility functions -----------------------------------------------


def setFxMode(n):
    global fxMode
    fxMode = n
# camera.image_effect = fxData[fxMode]
    buttons[6][5].setBg('fx-' + fxData[fxMode])


def setIsoMode(n):
    global isoMode
    isoMode = n
    # pycamera2 deals with analogue and digital gain, not ISO
    camera.set_controls = ({"AnalogueGain": int(isoData[isoMode][0]/100)})
    buttons[7][5].setBg('iso-' + str(isoData[isoMode][0]))
    buttons[7][7].rect = ((scaleWidth(isoData[isoMode][1] - 10),) +
                          buttons[7][7].rect[1:])


def saveSettings():
    try:
        outfile = open('cam.pkl', 'wb')
        # Use a dictionary (rather than pickling 'raw' values) so
        # the number & order of things can change without breaking.
        d = {'fx': fxMode,
             'iso': isoMode,
             'size': sizeMode,
             'store': storeMode}
        pickle.dump(d, outfile)
        outfile.close()
    except BaseException:
        pass


def loadSettings():
    try:
        infile = open('cam.pkl', 'rb')
        d = pickle.load(infile)
        infile.close()
        if 'fx' in d:
            setFxMode(d['fx'])
        if 'iso' in d:
            setIsoMode(d['iso'])
        if 'size' in d:
            sizeModeCallback(d['size'])
        if 'store' in d:
            storeModeCallback(d['store'])
    except BaseException:
        pass

# Scan files in a directory, locating JPEGs with names matching the
# software's convention (IMG_XXXX.JPG), returning a tuple with the
# lowest and highest indices (or None if no matching files).


def imgRange(path):
    min = 9999
    max = 0
    try:
        for file in os.listdir(path):
            if fnmatch.fnmatch(file, 'IMG_[0-9][0-9][0-9][0-9].JPG'):
                i = int(file[4:8])
                if (i < min):
                    min = i
                if (i > max):
                    max = i
    finally:
        return None if min > max else (min, max)

def processFile(job):
    try:
        if imageQueue.empty(): return
        filename = imageQueue.get()
        os.chown(filename, uid, gid) # Not working, why?
        os.chmod(filename, stat.S_IRUSR | stat.S_IWUSR |
             stat.S_IRGRP | stat.S_IROTH)
    except Exception as err:
        print("Could not process file. Photo might still exist, but belong to root.", err)
        quitCallback()

def takePicture():
    global busy, gid, loadIdx, saveIdx, scaled, sizeMode, storeMode, storeModePrior, uid, screen_height, screen_width

    if not os.path.isdir(pathData[storeMode]):
        try:
            os.makedirs(pathData[storeMode])
            # Set new directory ownership to pi user, mode to 755
            os.chown(pathData[storeMode], uid, gid)
            os.chmod(pathData[storeMode],
                     stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR |
                     stat.S_IRGRP | stat.S_IXGRP |
                     stat.S_IROTH | stat.S_IXOTH)
        except OSError as e:
            # errno = 2 if can't create folder
            print(errno.errorcode[e.errno])
            return

    # If this is the first time accessing this directory,
    # scan for the max index, start at next pos.
    if storeMode != storeModePrior:
        r = imgRange(pathData[storeMode])
        if r is None:
            saveIdx = 1
        else:
            saveIdx = r[1] + 1
            if saveIdx > 9999:
                saveIdx = 0
        storeModePrior = storeMode

    # Scan for next available image slot
    while True:
        filename = pathData[storeMode] + '/IMG_' + '%04d' % saveIdx + '.JPG'
        if not os.path.isfile(filename):
            break
        saveIdx += 1
        if saveIdx > 9999:
            saveIdx = 0

    #t = threading.Thread(target=spinner)
    #t.start()

    scaled = None
    try:
        # TODO: indicator that saving is happening
        imageQueue.put(filename)
        camera.capture_file(filename, format='jpeg', wait=False, signal_function=processFile)
        #processFile()
    except Exception as err:
        print(err)
        quitCallback()
    except OSError as err:
        print(err)
        quitCallback()
    finally:
        # Add error handling/indicator (disk full, etc.)
        pass
        #busy = False
        #t.join()

    pygame.display.update()
    loadIdx = saveIdx


# Initialization -----------------------------------------------------------
# Init framebuffer/touchscreen environment variables
os.putenv('SDL_VIDEODRIVER', 'fbcon')
# !!!!!!!ATTENTION!!!!!!!!
# When attached to an HDMI monitor, your TFT display will be /dev/fb1
# When operating on its own, your TFT display will be /dev/fb0
os.putenv('SDL_FBDEV', '/dev/fb0')
os.putenv('SDL_MOUSEDRV', 'TSLIB')
os.putenv('SDL_MOUSEDEV', '/dev/input/event3')

# Get user & group IDs for file & folder creation
# (Want these to be 'pi' or other user, not root)
s = os.getenv("SUDO_UID")
uid = int(s) if s else os.getuid()
s = os.getenv("SUDO_GID")
gid = int(s) if s else os.getgid()


# Init pygame and screen
pygame.init()
screen = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
pygame.mouse.set_visible(False)

# Init camera and set up default values
res = (screen_width, screen_height)
rgb = bytearray(screen_width * screen_height * 3)

# Set up Camera
camera = Picamera2()
# preview_config = camera.create_preview_configuration(
#    {"size": (screen_width, screen_height), "format": "BGR888"})
main_config = {"size": sizeData[sizeMode][0]}
lores_config = {"size": res}

still_config = camera.create_still_configuration(main_config, lores_config, display="lores")
camera.configure(still_config)
camera.still_configuration.enable_lores()
camera.still_configuration.lores.size = res
camera.still_configuration.align()
camera.start()

# Set up buttons

atexit.register(camera.stop)
# camera.resolution = sizeData[sizeMode][1]
# camera.crop       = sizeData[sizeMode][2]
# camera.crop       = (0.0, 0.0, 1.0, 1.0)
# Leave raw format at default YUV, don't touch, don't set to RGB!

# Load all icons at startup.
for file in os.listdir(iconPath):
    if fnmatch.fnmatch(file, '*.png'):
        icons.append(Icon(file.split('.')[0]))

# Assign Icons to Buttons, now that they're loaded
for s in buttons:        # For each screenful of buttons...
    for b in s:  # For each button on screen...
        for i in icons:  # For each icon...
            if b.bg == i.name:  # Compare names; match?
                b.iconBg = i  # Assign Icon to Button
                b.bg = None  # Name no longer used; allow garbage collection
            if b.fg == i.name:
                b.iconFg = i
                b.fg = None

loadSettings()  # Must come last; fiddles with Button/Icon states

# This array defines the custom function of the keyboard buttons for each
# screen
controls = [
    dict({pygame.K_UP: (imageCallback, -1),
          pygame.K_DOWN: (imageCallback, 1),
          pygame.K_b: (imageCallback, 0)
          }),  # 0 is photo playback
    dict({pygame.K_LEFT: (deleteCallback, True),
          pygame.K_RIGHT: (deleteCallback, False)
          }),  # 1 is delete confirmation
    dict({}),  # 2 is photo playback if no images are available
    dict({pygame.K_a: (takePicture, None)}),  # 3 is viewfinder mode
    dict({}),  # 4 is storage settings
    dict({pygame.K_UP: (sizeModeCallback, 1),
          pygame.K_DOWN: (sizeModeCallback, -1)
          }),  # 5 is size settings
    dict({pygame.K_UP: (fxCallback, 1),
          pygame.K_DOWN: (fxCallback, -1)
          }),  # 6 is effects settings
    dict({pygame.K_UP: (isoCallback, 1),
          pygame.K_DOWN: (isoCallback, -1)
          }),  # 7 is ISO settings
    dict({pygame.K_b: (quitCallback, None)})  # 8 is the quit screen

]
# Main loop ----------------------------------------------------------------

while (True):

    # Process touchscreen input
    while True:
        for event in pygame.event.get():
            if (event.type is KEYDOWN):
                # Execute the appropriate function for this key in the controls
                # array
                callbackTuple = controls[screenMode].get(event.key, None)
                if callbackTuple:
                    if callbackTuple[1] is not None:
                        callbackTuple[0](callbackTuple[1])
                    else:
                        callbackTuple[0]()
            # Some keys have default meaning if not overwritten
                if event.key == pygame.K_LEFT:
                    settingCallback(-1)
                elif event.key == pygame.K_RIGHT:
                    settingCallback(1)
                elif event.key == pygame.K_z:  # Always have a backup key to quit out of the program in development
                    quitCallback()
                elif event.key == pygame.K_a:  # Return to camera mode if shutter button is pressed
                    doneCallback()
        # If in viewfinder or settings modes, stop processing touchscreen
        # and refresh the display to show the live preview.  In other modes
        # (image playback, etc.), stop and refresh the screen only when
        # screenMode changes.
        if screenMode >= 3 or screenMode != screenModePrior:
            break

    # Refresh display
    if screenMode >= 3:  # Viewfinder or settings modes
        yuv420 = camera.capture_array("lores")
        rgb = cv2.cvtColor(yuv420, cv2.COLOR_YUV420p2RGB)
        # The image that comes out of cv2 is distorted and has the wrong size.
        # Good enough for a viewfinder, but I might need to do something about it later.
        img = pygame.image.frombuffer(rgb, camera.still_configuration.lores.size, 'RGB')
        if pygame.display.get_init():
            screen.fill(0)
            fillBlit((0,0,screen_width, screen_height), img, screen, True)
    elif screenMode < 2:  # Playback mode or delete confirmation
        img = scaled       # Show last-loaded image
        fitBlit((0,0,screen_width, screen_height), img, screen)
    else:                # 'No Photos' mode
        img = None         # You get nothing, good day sir

    # Overlay buttons on display and update
    for i, b in enumerate(buttons[screenMode]):
        b.draw(screen)
    pygame.display.update()

    screenModePrior = screenMode
